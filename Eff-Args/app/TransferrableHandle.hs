{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module TransferrableHandle where

import Control.Concurrent
  ( MVar,
    killThread,
    newEmptyMVar,
    putMVar,
    takeMVar,
  )
import Control.Monad (join)
import Data.Foldable (for_)
import Data.Function (fix)
import Data.Traversable (for)
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

example1 :: IO ()
example1 = do
  (b, rest) <- runH (\h -> break h anH)
  print ("Broke on", b)
  r <- runH rest
  print r

example2 :: IO ()
example2 = allViaUncons anH

forever :: (a -> IO b) -> a -> IO (b, H a b)
forever f = lify f (forever f)

allViaUncons :: (Show a, Show r) => (H a () -> IO r) -> IO ()
allViaUncons s = do
  uncons s >>= \case
    Left r -> print r
    Right (a, rest) -> do
      print a
      allViaUncons rest

race :: [IO r] -> IO r
race jobs = do
  result <- newEmptyMVar
  tids <- for jobs $ \job ->
    forkIO (job >>= putMVar result)
  r <- takeMVar result
  for_ tids killThread
  pure r

-- It's not safe to call the continuation more than once.  We need to
-- find a form of safe handler.
uncons ::
  (H a () -> IO r) ->
  IO (Either r (a, H a () -> IO r))
uncons f = do
  rvar <- newEmptyMVar
  avar <- newEmptyMVar

  ref <- do
    kify
      ( -- When the handler receives an a, the worker thread is
        -- implicitly paused
        \put -> put $ \a -> do
          -- We allocate a new handler
          kify
            ( \put' -> do
                -- We run the setup of the new handler in the main
                -- thread, because it determines the return value of
                -- uncons.  Because the worker thread is paused it
                -- can't return an "r" during this time, i.e. rvar
                -- will not become filled.
                putMVar avar $ do
                  pure
                    ( Right
                        ( -- We return the head
                          a,
                          -- and the "rest" handler is passed in by the
                          -- caller of uncons
                          \(MkH v') -> do
                            -- Unwrap the "rest" handler
                            v'' <- takeMVar v'
                            -- We place the "rest" handler inside the
                            -- new handler.  This implicitly unpauses
                            -- the thread, because it now has
                            -- something it can successfully takeMVar
                            -- of.
                            put' v''
                            -- We wait for the thread to complete
                            takeMVar rvar
                        )
                    )
            )
            -- Return () and the new handler
            (\h -> pure ((), h))
      )
      pure

  -- Run the worker thread
  _ <- forkIO $ do
    r <- f ref
    putMVar rvar r

  join $
    race
      [ takeMVar avar,
        do
          r <- takeMVar rvar
          pure $ do
            pure (Left r)
      ]

break1 ::
  forall a b r.
  H a () ->
  (H (Either a b) () -> IO r) ->
  IO (Either r (b, H (Either a b) () -> IO r))
break1 h f = do
  uncons f >>= \case
    Left r -> pure (Left r)
    Right (e, k) -> case e of
      Left a -> do
        readH h a
        break1 h k
      Right b -> pure (Right (b, k))

-- This must be wrong. What if we terminate without a b?
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
