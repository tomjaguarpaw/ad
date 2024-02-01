{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module TransferrableHandle where

import Control.Concurrent
  ( MVar,
    newEmptyMVar,
    putMVar,
    takeMVar,
  )
import Data.Function (fix)
import GHC.Conc (forkIO)
import Prelude hiding (break)

newtype H a b = MkH (MVar (a -> IO (b, H a b)))

readH :: H a b -> a -> IO b
readH (MkH ref) a = do
  f <- takeMVar ref
  (b', MkH h) <- f a
  h' <- takeMVar h
  putMVar ref h'
  pure b'

hify :: (a -> IO (b, H a b)) -> IO (H a b)
hify k = kify (\put -> put k) pure

kify :: (((a -> IO (b, H a b)) -> IO ()) -> IO ()) -> (H a b -> IO r) -> IO r
kify k k' = do
  v <- newEmptyMVar
  k (putMVar v)
  k' (MkH v)

lify :: (a -> IO b) -> (a' -> IO (b', H a' b')) -> a -> IO (b, H a' b')
lify f next a = do
  a' <- f a
  h <- hify next
  pure (a', h)

runH :: (Show a) => (H a () -> IO r) -> IO r
runH f = do
  h <- hify (forever print)
  f h

anH :: H (Either Int Int) () -> IO String
anH h = do
  readH h (Left 1)
  readH h (Left 2)
  readH h (Left 3)
  readH h (Right 4)
  readH h (Right 5)
  readH h (Left 6)

  pure "Hello"

foo :: IO ()
foo = do
  (b, rest) <- runH (\h -> break h anH)
  print ("Broke on", b)
  r <- runH rest
  print r

forever :: (a -> IO b) -> a -> IO (b, H a b)
forever f = lify f (forever f)

break ::
  forall a b r.
  H a () ->
  (H (Either a b) () -> IO r) ->
  IO (b, H (Either a b) () -> IO r)
break h f = do
  ret <- newEmptyMVar

  rvar <- newEmptyMVar

  kify
    ( \put -> do
        put $ fix $ \again -> \case
          Left a -> lify (readH h) again a
          Right b -> do
            kify
              ( \put' -> do
                  putMVar
                    ret
                    ( b,
                      \h' -> do
                        put' $ forever (readH h')
                        takeMVar rvar
                    )
              )
              (\r -> pure ((), r))
    )
    ( \ref -> do
        _ <- forkIO $ do
          r <- f ref
          putMVar rvar r
        pure ()
    )

  takeMVar ret
