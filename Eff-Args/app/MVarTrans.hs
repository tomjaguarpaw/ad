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

data State s r
  = Get () (s -> r)
  | Put s (() -> r)
  deriving (Functor)

runT ::
  (Monad (t IO), MonadTrans t) =>
  (Handle t -> IO r) ->
  t IO r
runT m = do
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

evalState :: s -> (Handle (Trans.State.StateT s) -> IO r) -> IO r
evalState sInit m = Trans.State.evalStateT (runT m) sInit

tryExc :: (Handle (Trans.Except.ExceptT e) -> IO r) -> IO (Either e r)
tryExc m = Trans.Except.runExceptT (runT m)

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
runExcExample = tryExc excExample

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
  tryExc $ \opexc ->
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

-- To demonstrate what happnes when we read from an MVar that will not
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
