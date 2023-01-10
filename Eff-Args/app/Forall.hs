{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}

module Forall where

import Control.Monad.Morph
import Control.Monad.ST
import Control.Monad.Trans.Except (ExceptT (ExceptT), runExceptT)
import Control.Monad.Trans.Reader (ReaderT (ReaderT, runReaderT))
import Control.Monad.Trans.State (StateT (StateT), runStateT)
import Control.Monad.Trans.Writer
import Data.Functor.Identity (Identity)
import Data.Kind (Type)
import Data.STRef (modifySTRef, newSTRef, readSTRef)

newtype Forall1 m r where
  Forall1 :: {unForall1 :: forall a. m a r} -> Forall1 m r

instance (forall a. Functor (m a)) => Functor (Forall1 m) where
  fmap f (Forall1 m) = Forall1 (fmap f m)

instance (forall a. Applicative (m a)) => Applicative (Forall1 m) where
  pure x = Forall1 (pure x)
  Forall1 f <*> Forall1 x = Forall1 (f <*> x)

instance (forall a. Monad (m a)) => Monad (Forall1 m) where
  Forall1 m >>= f = Forall1 (m >>= (unForall1 . f))

newtype ForallInside (t :: (Type -> Type) -> Type -> Type) m r where
  ForallInside :: (forall a. t (m a) r) -> ForallInside t m r

newtype Foo t = Foo (forall m a. ForallInside t m a -> t (Forall1 m) a)

example :: WriterT [Int] (ST s) ()
example = do
  ref <- lift (newSTRef 1)
  let tell' = (tell . pure) =<< lift (readSTRef ref)
      inc = lift (modifySTRef ref (+ 1))

  tell'
  inc
  tell'
  inc
  tell'

distributeTWriter :: Foo (WriterT w)
distributeTWriter = Foo $
  \case (ForallInside t) -> WriterT (Forall1 (runWriterT t))

distributeTState :: Foo (StateT s)
distributeTState = Foo $
  \case (ForallInside t) -> StateT (\s -> Forall1 (runStateT t s))

distributeTExcept :: Foo (ExceptT e)
distributeTExcept = Foo $
  \case (ForallInside t) -> ExceptT (Forall1 (runExceptT t))

distributeTReader :: Foo (ReaderT e)
distributeTReader = Foo $
  \case (ForallInside t) -> ReaderT (\r -> Forall1 (runReaderT t r))

distributeTWriter' :: (forall s. WriterT w (m s) r) -> WriterT w (Forall1 m) r
distributeTWriter' t = WriterT (Forall1 (runWriterT t))

runST' :: Forall1 ST r -> Identity r
runST' (Forall1 f) = pure (runST f)

example2 ::
  forall t r.
  MFunctor t =>
  (forall m. (forall s. t (m s) r) -> t (Forall1 m) r) ->
  (forall s. t (ST s) r) ->
  t Identity r
example2 distributeT e = hoist runST' (distributeT e)

example3 :: ((), [Int])
example3 = runWriter (example2 distributeTWriter' example)

-- Doesn't type check
-- example2 = hoist (pure . runST) example
