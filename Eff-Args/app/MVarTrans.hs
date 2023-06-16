{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module MVarTrans where

import Control.Concurrent
import Control.Exception
  ( AssertionFailed (AssertionFailed),
    SomeException,
    throwIO,
    try,
  )
import Control.Monad (when)
import Control.Monad.Trans (MonadTrans, lift)
import qualified Control.Monad.Trans.Except as Trans.Except
import Control.Monad.Trans.Free
import qualified Control.Monad.Trans.State as Trans.State
import Data.Function
import Data.Functor.Identity (Identity (Identity))
import System.Mem (performGC)

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

multiCallsNotDetected :: ((b -> IO ()) -> IO ()) -> IO b
multiCallsNotDetected k = do
  mvar <- newEmptyMVar

  let putIt = putMVar mvar
      getIt = takeMVar mvar

  k putIt
  getIt

type Handled t = forall b. t IO b -> IO b

data State s r
  = Get () (s -> r)
  | Put s (() -> r)
  deriving (Functor)

eval ::
  (Monad (t IO), MonadTrans t) =>
  (Handled t -> IO r) ->
  t IO r
eval m = do
  recv <- lift $ do
    mvar <- newEmptyMVar
    let _ = mvar
    _ <- forkIO $ do
      let handled op = onlyOneCallAllowed $ \k -> putMVar mvar (Left (fmap k op))
      r <- m handled
      putMVar mvar (Right r)

    pure (lift (takeMVar mvar))

  fix $ \loop -> do
    recv >>= \case
      Left l -> do
        io <- l
        lift io
        loop
      Right r -> pure r

evalState :: s -> (Handled (Trans.State.StateT s) -> IO r) -> IO r
evalState sInit m = Trans.State.evalStateT (eval m) sInit

tryExc :: (Handled (Trans.Except.ExceptT e) -> IO r) -> IO (Either e r)
tryExc m = Trans.Except.runExceptT (eval m)

stateExample :: Handled (Trans.State.StateT Int) -> IO ()
stateExample st = do
  s0 <- st Trans.State.get
  putStrLn ("Initially " ++ show s0)
  st (Trans.State.modify' (+ 1))
  s1 <- st Trans.State.get
  putStrLn ("Then " ++ show s1)
  st (Trans.State.modify' (+ 1))
  s2 <- st Trans.State.get
  putStrLn ("Then again " ++ show s2)

runStateExample :: IO ()
runStateExample = evalState 0 stateExample

excExample :: Handled (Trans.Except.ExceptT String) -> IO ()
excExample op = do
  putStrLn "Running..."
  _ <- op (Trans.Except.throwE "An exception")
  putStrLn "Still running?"

runExcExample :: IO (Either String ())
runExcExample = tryExc excExample

mixedExample ::
  Handled (Trans.Except.ExceptT String) ->
  Handled (Trans.State.StateT Int) ->
  IO Int
mixedExample opexc opst = do
  s0 <- opst Trans.State.get
  putStrLn ("Initially " ++ show s0)

  opst (Trans.State.modify (+ 1))
  s1 <- opst Trans.State.get
  when (s1 > 1) (opexc (Trans.Except.throwE "s1"))

  opst (Trans.State.modify (+ 1))
  s2 <- opst Trans.State.get
  when (s2 > 1) (opexc (Trans.Except.throwE "s2"))

  pure s2

runMixedExample :: IO (Either String Int)
runMixedExample =
  tryExc $ \opexc ->
    evalState 0 $ \opst ->
      mixedExample opexc opst

data Id r = Id () (() -> r)
  deriving (Functor)

freeT :: (Functor f, Monad m) => f a -> FreeT f m a
freeT = FreeT . pure . fmap pure . Free

failExample :: IO ()
failExample = do
  f <-
    runFreeT
      ( eval
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
