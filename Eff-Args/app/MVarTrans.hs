{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module MVarTrans where

import Control.Concurrent
import Control.Exception hiding (Handler)
import Control.Monad
import Control.Monad.Trans (MonadTrans, lift)
import qualified Control.Monad.Trans.Except as Trans.Except
import Control.Monad.Trans.Free
import qualified Control.Monad.Trans.State as Trans.State
import Data.Function
import Data.Functor.Identity (Identity (Identity))
import System.Mem

main :: IO ()
main = do
  mvar <- newEmptyMVar

  let r = putMVar mvar ()

  _ <- forkIO $ do
    try (takeMVar mvar) >>= \case
      Left e -> print (e :: SomeException)
      Right {} -> pure ()
    r

  threadDelay 1
  performGC
  threadDelay 1

type Handler t = t IO (IO ()) -> IO ()

onlyOneCallAllowed :: ((b -> IO ()) -> IO ()) -> IO b
onlyOneCallAllowed k = do
  mvar <- newEmptyMVar

  let putIt b = do
        tid <- myThreadId
        putMVar mvar (b, tid)

      getIt = do
        (b, _) <- takeMVar mvar
        _ <- forkIO $
          fix $ \loop -> do
            (_, tid) <- takeMVar mvar
            throwTo tid (AssertionFailed "called a second time")
            loop
        pure b

  k putIt
  getIt

makeOpM0 :: Functor (t IO) => t IO b -> Handler t -> IO b
makeOpM0 op send = onlyOneCallAllowed (send . flip fmap op)

type Handled t = forall b. t IO b -> IO b

data State s r
  = Get () (s -> r)
  | Put s (() -> r)
  deriving (Functor)

evalM ::
  (Monad (t IO), MonadTrans t) =>
  (Handler t -> IO r) ->
  t IO r
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

evalMHandled :: (MonadTrans t, Monad (t IO)) => (Handled t -> IO r) -> t IO r
evalMHandled m = evalM (\handler -> m (flip makeOpM0 handler))

iterTrans :: Functor (t IO) => t IO r -> Handler t -> IO r
iterTrans t handler = do
  mvar <- newEmptyMVar
  handler (fmap (putMVar mvar) t)
  takeMVar mvar

evalStateM :: s -> (Handled (Trans.State.StateT s) -> IO r) -> IO r
evalStateM sInit m = Trans.State.evalStateT (evalMHandled m) sInit

tryExcM :: (Handled (Trans.Except.ExceptT e) -> IO r) -> IO (Either e r)
tryExcM m = Trans.Except.runExceptT (evalMHandled m)

stateExampleM :: Handled (Trans.State.StateT Int) -> IO ()
stateExampleM st = do
  s0 <- st Trans.State.get
  putStrLn ("Initially " ++ show s0)
  st (Trans.State.modify' (+ 1))
  s1 <- st Trans.State.get
  putStrLn ("Then " ++ show s1)
  st (Trans.State.modify' (+ 1))
  s2 <- st Trans.State.get
  putStrLn ("Then again " ++ show s2)

runStateExampleM :: IO ()
runStateExampleM = evalStateM 0 stateExampleM

excExampleM :: Handled (Trans.Except.ExceptT String) -> IO ()
excExampleM op = do
  putStrLn "Running..."
  _ <- op (Trans.Except.throwE "An exception")
  putStrLn "Still running?"

runExcExampleM :: IO (Either String ())
runExcExampleM = tryExcM excExampleM

mixedExampleM ::
  Handled (Trans.Except.ExceptT String) ->
  Handled (Trans.State.StateT Int) ->
  IO Int
mixedExampleM opexc opst = do
  s0 <- opst Trans.State.get
  putStrLn ("Initially " ++ show s0)

  opst (Trans.State.modify (+ 1))
  s1 <- opst Trans.State.get
  when (s1 > 1) (opexc (Trans.Except.throwE "s1"))

  opst (Trans.State.modify (+ 1))
  s2 <- opst Trans.State.get
  when (s2 > 1) (opexc (Trans.Except.throwE "s2"))

  pure s2

runMixedExampleM :: IO (Either String Int)
runMixedExampleM =
  tryExcM $ \opexc ->
    evalStateM 0 $ \opst ->
      mixedExampleM opexc opst

data Id r = Id () (() -> r)
  deriving (Functor)

freeT :: (Functor f, Monad m) => f a -> FreeT f m a
freeT = FreeT . pure . fmap pure . Free

failExampleM :: IO ()
failExampleM = do
  f <-
    runFreeT
      ( evalMHandled
          ( \op -> do
              putStrLn "Running"
              op (freeT (Identity ()))
              putStrLn "Middle running"
              op (freeT (Identity ()))
              putStrLn "Finished running"
          )
      )
  case f of
    Pure () -> pure ()
    Free (Identity k) -> do
      let k' = do
            _ <- runFreeT k
            pure ()
      k'
      k'
      putStrLn "Finished"

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
