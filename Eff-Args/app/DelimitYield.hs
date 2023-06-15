{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UnboxedTuples #-}

module DelimitYield where

import qualified Control.Monad.Trans.State as Trans.State
import qualified Control.Monad.Trans.Except as Trans.Except

import Control.Monad.Trans
import Control.Monad (join, when)
import GHC.Exts
import GHC.Types

type Handled t = forall b. t IO b -> IO b

type YieldTag a b r = (PromptTag r, a -> (IO b -> IO r) -> IO r)

data PromptTag a = PromptTag (PromptTag# a)

newPromptTag :: IO (PromptTag a)
newPromptTag = IO $ \s -> case newPromptTag# s of
  (# s', promptTag# #) -> (# s', PromptTag promptTag# #)

prompt :: PromptTag a -> IO a -> IO a
prompt (PromptTag p) (IO m) = IO (prompt# p m)

control0 :: PromptTag a -> ((IO b -> IO a) -> IO a) -> IO b
control0 (PromptTag p) handle = IO (control0# p (\k -> unIO (handle (IO . k . unIO))))

unIO :: IO a -> State# RealWorld -> (# State# RealWorld, a #)
unIO (IO m) = m

withScopedEffect ::
  (a -> (IO b -> IO r) -> IO r) -> ((a -> IO b) -> IO r) -> IO r
withScopedEffect handler body = do
  promptTag <- newPromptTag
  prompt promptTag (body (\e -> control0 promptTag (\k -> handler e (prompt promptTag . k))))

evalMHandled ::
  (MonadTrans t, Monad (t IO)) =>
  ((forall b. t IO b -> IO b) -> IO r) ->
  t IO r
evalMHandled body = do
  promptTag <- lift newPromptTag
  join $ lift $ prompt promptTag (fmap pure (body (\act -> control0 promptTag (\k -> pure $ do
                                                                                  b <- act
                                                                                  join $ lift (prompt promptTag (k (pure b)))
                                                                                  ))))

example :: IO ()
example = withScopedEffect (\a k -> putStrLn a *> k (pure ()) *> k (pure ())) $ \y -> do
  y "y Hello"
  putStrLn "Inside"
  y "y Bye"
  putStrLn "Finishing Inside"

evalStateM :: s -> (Handled (Trans.State.StateT s) -> IO r) -> IO r
evalStateM sInit m = Trans.State.evalStateT (evalMHandled m) sInit

tryExcM :: (Handled (Trans.Except.ExceptT e) -> IO r) -> IO (Either e r)
tryExcM m = Trans.Except.runExceptT (evalMHandled m)


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

yield :: YieldTag b a r -> b -> IO a
yield (p, handler) = control0 p . handler
