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
import qualified Control.Monad.Trans.State as Trans.State
import Data.Function
import qualified Streaming.Prelude
import System.Mem (performGC)

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

type Handle t = forall b. t IO b -> IO b

runT ::
  forall t r.
  (Monad (t IO), MonadTrans t) =>
  (Handle t -> IO r) ->
  t IO r
runT block = do
  mvar <- lift newEmptyMVar
  let _ = mvar :: MVar (t IO (Maybe r))
  _ <- lift $
    forkIO $ do
      let handle :: forall a. t IO a -> IO a
          handle op = onlyOneCallAllowed x
            where
              x :: (a -> IO ()) -> IO ()
              x send = putMVar mvar $ do
                a <- op
                lift (send a)
                pure Nothing

      r <- block handle
      putMVar mvar (pure (Just r))

  untilJust $ do
    t <- lift (takeMVar mvar)
    t

untilJust :: Monad m => m (Maybe r) -> m r
untilJust receive =
  fix $ \loop -> do
    receive >>= \case
      Nothing -> loop
      Just r -> pure r

evalState :: s -> (Handle (Trans.State.StateT s) -> IO r) -> IO r
evalState sInit m = Trans.State.evalStateT (runT m) sInit

runExcept :: (Handle (Trans.Except.ExceptT e) -> IO r) -> IO (Either e r)
runExcept m = Trans.Except.runExceptT (runT m)

stateExample :: Handle (Trans.State.StateT Int) -> IO ()
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

excExample :: Handle (Trans.Except.ExceptT String) -> IO ()
excExample op = do
  putStrLn "Running..."
  _ <- op (Trans.Except.throwE "An exception")
  putStrLn "Still running?"

runExcExample :: IO (Either String ())
runExcExample = runExcept excExample

mixedExample ::
  Handle (Trans.Except.ExceptT String) ->
  Handle (Trans.State.StateT Int) ->
  IO Int
mixedExample opexc opst = do
  s0 <- opst Trans.State.get
  putStrLn ("Initially " ++ show s0)

  opst (Trans.State.modify (+ 1))
  s1 <- opst Trans.State.get
  putStrLn ("Then " ++ show s1)
  when (s1 > 1) (opexc (Trans.Except.throwE "s1"))

  opst (Trans.State.modify (+ 1))
  s2 <- opst Trans.State.get
  putStrLn ("Then " ++ show s2)
  when (s2 > 1) (opexc (Trans.Except.throwE "s2"))

  pure s2

runMixedExample :: IO (Either String Int)
runMixedExample =
  runExcept $ \opexc ->
    evalState 0 $ \opst ->
      mixedExample opexc opst

failExample :: IO ()
failExample = do
  let stream = runT $ \op -> do
        op (Streaming.Prelude.yield ())
        op (Streaming.Prelude.yield ())

  putStrLn "Running to first yield"
  Streaming.Prelude.uncons stream >>= \case
    Nothing -> error "should have elements"
    Just ((), rest) -> do
      putStrLn "Running to second yield"
      _ <- Streaming.Prelude.uncons rest
      putStrLn "Running to second yield again"
      _ <- Streaming.Prelude.uncons rest
      putStrLn "Finished"

-- How to get nested exception propagation?
forkExcept :: IO () -> IO ThreadId
forkExcept io = do
  tid <- myThreadId
  forkFinally io (either (throwTo tid) pure)

-- The exception is propagated
nest1 :: IO ()
nest1 = do
  _ <- forkExcept $ do
    throwIO (AssertionFailed "end thread")

  threadDelay 1
  putStrLn "Finished"

-- The exception is not propagated because the parent thread,
-- i.e. first forked thread, dies before it can receive the exception
-- rethrown at the termination of the second forked thread.
nest2 :: IO ()
nest2 = do
  _ <- forkExcept $ do
    _ <- forkExcept $ do
      throwIO (AssertionFailed "end thread")
    pure ()

  threadDelay 1
  putStrLn "Finished"

-- The exception is propagated because the parent thread is still
-- around.
nest3 :: IO ()
nest3 = do
  _ <- forkExcept $ do
    _ <- forkExcept $ do
      throwIO (AssertionFailed "end thread")

    threadDelay 1

  threadDelay 1
  putStrLn "Finished"

-- To demonstrate what happens when we read from an MVar that will not
-- be written to
blockedIndefinitely :: IO ()
blockedIndefinitely = do
  mvar <- newEmptyMVar

  _ <- forkIO $ do
    try (takeMVar mvar) >>= \case
      Left e -> do
        putStrLn ("Caught exception: " ++ show (e :: SomeException))
      Right {} -> pure ()
    putMVar mvar ()

  threadDelay 1
  performGC
  threadDelay 1
