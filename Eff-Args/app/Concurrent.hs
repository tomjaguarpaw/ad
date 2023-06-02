import Control.Concurrent.MVar
import Control.Concurrent hiding (yield)

import Data.Text


-- (>>~) of pipes
coroutine ::
  ((a -> IO b) -> IO r) ->
  (a -> (b -> IO a) -> IO r) ->
  IO r
coroutine k1 k2 = do
  m1 <- newEmptyMVar
  m2 <- newEmptyMVar
  mr <- newEmptyMVar

  _ <- forkIO $ do
    r <- k1 $ \a -> do putMVar m1 a; takeMVar m2
    putMVar mr r

  _ <- forkIO $ do
    a <- takeMVar m1
    r <- k2 a $ \b -> do putMVar m2 b; takeMVar m1
    putMVar mr r

  takeMVar mr

example :: IO String
example =
  coroutine
  (\yield -> do
      b <- yield "a1"
      putStrLn ("b: " ++ b)
      b2 <- yield "a2"
      putStrLn ("b2: " ++ b2)
      b3 <- yield "a3"
      putStrLn ("b3: " ++ b3)
      pure "First"
  )
  (\a yield -> do
      putStrLn ("a: " ++ a)
      a1 <- yield "b1"
      putStrLn ("a1: " ++ a1)
      a2 <- yield "b2"
      putStrLn ("a2: " ++ a2)
      a3 <- yield "b3"
      putStrLn ("a3: " ++ a3)
      pure "Second"
  )
