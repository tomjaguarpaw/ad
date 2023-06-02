{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module MVarTrans where

import Data.Function
import Data.Void
import Control.Concurrent
import Control.Exception hiding (Handler)
import Control.Monad
import Control.Monad.Trans (lift, MonadTrans)
import Control.Monad.Trans.Free
import qualified Control.Monad.Trans.State as Trans.State
import qualified Control.Monad.Trans.Except as Trans.Except
import System.Mem

main :: IO ()
main = do
  mvar <- newEmptyMVar

  let r = putMVar mvar ()

  _ <- forkIO $ do
    try (takeMVar mvar) >>= \case
      Left e -> print (e :: SomeException)
      Right{} -> pure ()
    r

  threadDelay 1
  performGC
  threadDelay 1

type Op f = f (IO ()) -> IO ()

type Handler t = t IO (IO ()) -> IO ()

onlyOneCallAllowed :: ((b -> IO ()) -> IO ()) -> IO b
onlyOneCallAllowed k = do
  mvar <- newEmptyMVar

  let putIt b = do
        tid <- myThreadId
        putMVar mvar (b, tid)

      getIt = do
        (b, _) <- takeMVar mvar
        _ <- forkIO $ fix $ \loop -> do
          (_, tid) <- takeMVar mvar
          throwTo tid (AssertionFailed "called a second time")
          loop
        pure b

  k putIt
  getIt

makeOp ::
  (a -> (b -> IO ()) -> fio) ->
  (fio -> IO ()) ->
  a ->
  IO b
makeOp op send a = onlyOneCallAllowed (send . op a)

makeOpM ::
  Functor (t IO) =>
  (a -> t IO b) ->
  Handler t ->
  a ->
  IO b
makeOpM op send a = onlyOneCallAllowed (send . flip fmap (op a))

makeOpM0 :: Functor (t IO) => t IO b -> Handler t -> IO b
makeOpM0 op send = makeOpM (const op) send ()

data State s r =
    Get () (s -> r)
  | Put s (() -> r)
  deriving Functor

get :: Op (State s) -> IO s
get op = makeOp Get op ()

put :: Op (State s) -> s -> IO ()
put = makeOp Put

modify :: Op (State s) -> (s -> s) -> IO ()
modify op f = do
  s <- get op
  put op (f s)

eval :: forall f r. Functor f => (Op f -> IO r) -> FreeT f IO r
eval f = do
  recv <- lift $ do
    mvar <- newEmptyMVar
    let _ = mvar :: MVar (Either (f (IO ())) r)
    _ <- forkIO $ do
      r <- f (putMVar mvar . Left)
      putMVar mvar (Right r)

    pure (lift (takeMVar mvar))

  fix $ \loop -> do
    recv >>= \case
      Left l -> do
        io <- liftF l
        lift io
        loop
      Right r -> pure r

evalM ::
  (Monad (t IO), MonadTrans t) =>
  (Handler t -> IO r) -> t IO r
evalM f = do
  recv <- lift $ do
    mvar <- newEmptyMVar
    let _ = mvar
    _ <- forkIO $ do
      r <- f (putMVar mvar . Left)
      putMVar mvar (Right r)

    pure (lift (takeMVar mvar))

  fix $ \loop -> do
    recv >>= \case
      Left l -> do
        io <- l
        lift io
        loop
      Right r -> pure r

-- This doesn't work!
unevalEasy :: Functor f => FreeT f IO () -> Op f -> IO ()
unevalEasy f op = Control.Monad.Trans.Free.iterT op f

-- This doesn't work!
unevalComplex :: Functor f => FreeT f IO r -> Op f -> IO r
unevalComplex f op = do
  mvar <- newEmptyMVar
  flip Control.Monad.Trans.Free.iterT f $ \fio -> do
    let fio' = flip fmap fio $ \ior -> do
          r <- ior
          putMVar mvar r

    op fio'
    takeMVar mvar

iterT :: Functor f => FreeT f IO r -> Op f -> IO r
iterT f op = do
  mvar <- newEmptyMVar

  -- All but the first iteration of this loop actually run in the
  -- handler thread, not this thread!
  flip fix f $ \again f' -> do
    runFreeT f' >>= \case
      Pure r -> putMVar mvar r
      Free k -> op (fmap again k)

  takeMVar mvar

iterTrans :: Functor (t IO) => t IO r -> Handler t -> IO r
iterTrans t handler = do
  mvar <- newEmptyMVar
  handler (fmap (putMVar mvar) t)
  takeMVar mvar

evalFoldFree ::
  (MonadTrans t, Monad (t IO), Functor f) =>
  (forall n x. Monad n => f x -> t n x) ->
  (t IO a -> ioa) ->
  (Op f -> IO a) ->
  ioa
evalFoldFree d r = r . foldFreeT d . eval

evalState :: s -> (Op (State s) -> IO r) -> IO r
evalState sInit =
  evalFoldFree d (flip Trans.State.evalStateT sInit)
  where
    d :: Monad m => State a b -> Trans.State.StateT a m b
    d = \case
        Get () k -> fmap k Trans.State.get
        Put s k -> fmap k (Trans.State.put s)

stateExample :: Op (State Int) -> IO ()
stateExample op = do
  s0 <- get op
  putStrLn ("Initially " ++ show s0)
  modify op (+ 1)
  s1 <- get op
  putStrLn ("Then " ++ show s1)
  modify op (+ 1)
  s2 <- get op
  putStrLn ("Then again " ++ show s2)

stateExampleM :: Handler (Trans.State.StateT Int) -> IO ()
stateExampleM op = do
  let make = flip makeOpM0 op
  s0 <- make Trans.State.get
  putStrLn ("Initially " ++ show s0)
  makeOpM0 (Trans.State.modify' (+ 1)) op
  s1 <- make Trans.State.get
  putStrLn ("Then " ++ show s1)
  makeOpM Trans.State.modify' op (+ 1)
  s2 <- make Trans.State.get
  putStrLn ("Then again " ++ show s2)

runStateExample :: IO ()
runStateExample = evalState (0 :: Int) stateExample

data Exc e r = Throw e (Void -> r)
  deriving Functor

throwExc :: Op (Exc e) -> e -> IO a
throwExc op e = fmap absurd (makeOp Throw op e)

tryExc :: (Op (Exc e) -> IO a) -> IO (Either e a)
tryExc = evalFoldFree d Trans.Except.runExceptT
  where
    d :: Monad m => Exc a b -> Trans.Except.ExceptT a m b
    d = \case
      Throw e k -> fmap k (Trans.Except.throwE e)

excExample :: Op (Exc String) -> IO ()
excExample op = do
  putStrLn "Running..."
  _ <- throwExc op "An exception"
  putStrLn "Still running?"

runExcExample :: IO (Either String ())
runExcExample = tryExc excExample

mixedExample :: Op (Exc String) -> Op (State Int) -> IO Int
mixedExample opexc opst = do
  s0 <- get opst
  putStrLn ("Initially " ++ show s0)

  modify opst (+ 1)
  s1 <- get opst
  when (s1 > 1) (throwExc opexc "s1")

  modify opst (+ 1)
  s2 <- get opst
  when (s2 > 1) (throwExc opexc "s2")

  pure s2

runMixedExample :: IO (Either String Int)
runMixedExample =
  tryExc $ \opexc ->
    evalState (0 :: Int) $ \opst ->
      mixedExample opexc opst

data Id r = Id () (() -> r)
  deriving Functor

failExample :: IO ()
failExample = do
  f <- runFreeT (eval (\op -> do
                          putStrLn "Running"
                          makeOp Id op ()
                          putStrLn "Middle running"
                          makeOp Id op ()
                          putStrLn "Finished running"
                      ))
  case f of
    Pure () -> pure ()
    Free (Id () k) -> do
      let k' = do
            _ <- runFreeT (k ())
            pure ()
      k'
      k'
      putStrLn "Finished"

evalStateFused :: s -> (Op (State s) -> IO r) -> IO r
evalStateFused sInit f = do
  recv <- newEmptyMVar

  _ <- forkIO $ do
    r <- f (putMVar recv . Left)
    putMVar recv (Right r)

  flip fix sInit $ \loop !s -> do
    takeMVar recv >>= \case
      Left l -> case l of
        Get () k -> do
          k s
          loop s
        Put s' k -> do
          k ()
          loop s'
      Right r -> pure r

tryExcFused :: (Op (Exc e) -> IO r) -> IO (Either e r)
tryExcFused f = do
  recv <- newEmptyMVar

  _ <- forkIO $ do
    r <- f (putMVar recv . Left)
    putMVar recv (Right r)

  takeMVar recv >>= \case
    Left (Throw e _) -> pure (Left e)
    Right r -> pure (Right r)

-- How to get nested exception propagation?
forkExcept :: IO () -> IO ThreadId
forkExcept io = do
  tid <- myThreadId
  forkFinally io (either (throwTo tid) pure)

nest1 :: IO ()
nest1 = do
  _ <- forkExcept $ do
    throwIO (AssertionFailed "end thread")

  threadDelay 1
  putStrLn "Finished"

nest2 :: IO ()
nest2 = do
  _ <- forkExcept $ do
    _ <- forkExcept $ do
      error "end thread"
    pure ()

  threadDelay 100000
  putStrLn "Finished"
