{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Main where

import Control.Monad.Trans.Class (MonadTrans)
import Control.Monad.Trans.State.Strict (StateT)
import qualified Control.Monad.Trans.State.Strict as State
import Data.Coerce (coerce)
import Data.Functor.Identity (Identity (runIdentity))
import Data.Kind (Type)

-- These "myModify" functions all compile to the same code --
-- *exactly* the same code, i.e. they share the implementation (which
-- is just a constant)!  Good.

myModifyMTL :: Int
myModifyMTL =
  runIdentity $
    flip State.evalStateT 0 $ do
      s <- State.get
      State.put $! s + 1
      State.get

myModifyNewtype :: Int
myModifyNewtype =
  runIdentity $
    unE $
      flip State.evalStateT 0 $
        unL $
          unB $ do
            s <- Bm $ Lm State.get
            Bm $ Lm $ State.put $! s + 1
            Bm $ Lm State.get

myModifyEff :: Int
myModifyEff =
  runIdentity $
    unMkEff $
      flip State.evalStateT 0 $
        unMkEff $
          unMkEff @(Branch (Leaf (StateT Int)) Empty) $ do
            s <- MkEff $ MkEff State.get
            MkEff $ MkEff $ State.put $! s + 1
            MkEff $ MkEff State.get

-- These "mySum" functions don't all compile to the same code.  Bad!
-- "mySumMTL" and "mySumNewtype" compile to the same code but it's not
-- shared.  That's fine.  I don't care.  I really care that "mySumEff"
-- compiles to the same code, but it doesn't.  It compiles to an
-- inefficient loop with allocation.

-- The choice of loop combinator is not particularly important.  It
-- just needs to be something that makes the below programs
-- non-trivial, so we can see how well the optimizer works.
myfor :: (Applicative f) => Int -> (Int -> f a) -> f ()
myfor 0 _ = pure ()
myfor n b = b n *> myfor (n - 1) b

mySumMTL :: Int
mySumMTL =
  runIdentity $
    flip State.evalStateT 0 $ do
      myfor 10 $ \i -> do
        s <- State.get
        State.put $! s + i
      State.get

mySumNewtype :: Int
mySumNewtype =
  runIdentity $
    unE $
      flip State.evalStateT 0 $
        unL $
          unB $ do
            myfor 10 $ \i -> do
              s <- Bm $ Lm State.get
              Bm $ Lm $ State.put $! s + i
            Bm $ Lm State.get

mySumEff :: Int
mySumEff =
  runIdentity $
    unMkEff $
      flip State.evalStateT 0 $
        unMkEff $
          unMkEff @(Branch (Leaf (StateT Int)) Empty) $
            do
              myfor 10 $ \i -> do
                s <- MkEff $ MkEff State.get
                MkEff $ MkEff $ State.put $! s + i
              MkEff $ MkEff State.get

-- Definitions for the "Newtype" versions

newtype Lt t m a = Lm {unL :: t m a}
  deriving newtype (Functor, Applicative, Monad)

newtype Et m a = Em {unE :: m a}
  deriving newtype (Functor, Applicative, Monad)

newtype Bt t1 t2 m a = Bm {unB :: t1 (t2 m) a}
  deriving newtype (Functor, Applicative, Monad)

-- Definitions for the "Eff" versions, that use Eff, an "effect
-- system"

-- A type that encodes the structure of a composed series of monad
-- transformers
data Effects
  = Branch Effects Effects
  | Leaf ((Type -> Type) -> Type -> Type)
  | Empty

-- A singleton type for Effects
data SEffects i where
  SBranch :: (SingI i1, SingI i2) => SEffects (Branch i1 i2)
  SLeaf :: (MonadTrans t) => SEffects (Leaf t)
  SEmpty :: SEffects Empty

-- For passing the singleton implicitly, like in the singletons
-- library
class SingI i where
  sing :: SEffects i

instance (MonadTrans t) => SingI (Leaf t) where
  sing = SLeaf

instance (SingI t1, SingI t2) => SingI (Branch t1 t2) where
  sing = SBranch

instance SingI Empty where
  sing = SEmpty

newtype Eff es m a = MkEff {unMkEff :: EffF es m a}

type family EffF (es :: Effects) m where
  EffF Empty m = m
  EffF (Leaf t) m = t m
  EffF (Branch s1 s2) m = Eff s1 (Eff s2 m)

coerceFmapEmpty ::
  forall a b m. (Functor m) => (a -> b) -> Eff Empty m a -> Eff Empty m b
coerceFmapEmpty = coerce (fmap @m @a @b)

coerceFmapLeaf ::
  forall a b t m.
  (MonadTrans t, Monad m) =>
  (a -> b) ->
  Eff (Leaf t) m a ->
  Eff (Leaf t) m b
coerceFmapLeaf = coerce (fmap @(t m) @a @b)

coerceFmapBranch ::
  forall a b s1 s2 m.
  (SingI s1, SingI s2, Monad m) =>
  (a -> b) ->
  Eff (Branch s1 s2) m a ->
  Eff (Branch s1 s2) m b
coerceFmapBranch = coerce (fmap @(Eff s1 (Eff s2 m)) @a @b)

coercePureEmpty :: forall a m. (Applicative m) => a -> Eff Empty m a
coercePureEmpty = coerce (pure :: a -> m a)

coercePureLeaf ::
  forall a t m.
  (MonadTrans t, Monad m) =>
  a ->
  Eff (Leaf t) m a
coercePureLeaf = coerce (pure :: a -> t m a)

coercePureBranch ::
  forall a s1 s2 m.
  (Monad m, SingI s1, SingI s2) =>
  a ->
  Eff (Branch s1 s2) m a
coercePureBranch = coerce (pure :: a -> Eff s1 (Eff s2 m) a)

coerceAndThenEmpty ::
  forall m a b. (Applicative m) => Eff Empty m a -> Eff Empty m b -> Eff Empty m b
coerceAndThenEmpty = coerce ((*>) :: m a -> m b -> m b)

coerceAndThenLeaf ::
  forall t m a b.
  (MonadTrans t, Monad m) =>
  Eff (Leaf t) m a ->
  Eff (Leaf t) m b ->
  Eff (Leaf t) m b
coerceAndThenLeaf = coerce ((*>) :: t m a -> t m b -> t m b)

coerceAndThenBranch ::
  forall s1 s2 m a b.
  (SingI s1, SingI s2, Monad m) =>
  Eff (Branch s1 s2) m a ->
  Eff (Branch s1 s2) m b ->
  Eff (Branch s1 s2) m b
coerceAndThenBranch =
  coerce
    ( (*>) ::
        Eff s1 (Eff s2 m) a ->
        Eff s1 (Eff s2 m) b ->
        Eff s1 (Eff s2 m) b
    )

coerceAppEmpty ::
  forall m a b. (Applicative m) => Eff Empty m (a -> b) -> Eff Empty m a -> Eff Empty m b
coerceAppEmpty = coerce ((<*>) :: m (a -> b) -> m a -> m b)

coerceAppLeaf ::
  forall t m a b.
  (MonadTrans t, Monad m) =>
  Eff (Leaf t) m (a -> b) ->
  Eff (Leaf t) m a ->
  Eff (Leaf t) m b
coerceAppLeaf = coerce ((<*>) :: t m (a -> b) -> t m a -> t m b)

coerceAppBranch ::
  forall s1 s2 m a b.
  (SingI s1, SingI s2, Monad m) =>
  Eff (Branch s1 s2) m (a -> b) ->
  Eff (Branch s1 s2) m a ->
  Eff (Branch s1 s2) m b
coerceAppBranch =
  coerce
    ( (<*>) ::
        Eff s1 (Eff s2 m) (a -> b) ->
        Eff s1 (Eff s2 m) a ->
        Eff s1 (Eff s2 m) b
    )

coerceBindEmpty ::
  forall m a b. (Monad m) => Eff Empty m a -> (a -> Eff Empty m b) -> Eff Empty m b
coerceBindEmpty = coerce ((>>=) @m @a @b)

coerceBindLeaf ::
  forall t m a b.
  (MonadTrans t, Monad m) =>
  Eff (Leaf t) m a ->
  (a -> Eff (Leaf t) m b) ->
  Eff (Leaf t) m b
coerceBindLeaf = coerce ((>>=) @(t m) @a @b)

coerceBindBranch ::
  forall s1 s2 m a b.
  (SingI s1, SingI s2, Monad m) =>
  Eff (Branch s1 s2) m a ->
  (a -> Eff (Branch s1 s2) m b) ->
  Eff (Branch s1 s2) m b
coerceBindBranch =
  coerce ((>>=) @(Eff s1 (Eff s2 m)) @a @b)

instance (SingI es, Monad m) => Functor (Eff es m) where
  fmap = case sing @es of
    SEmpty -> coerceFmapEmpty
    SBranch -> coerceFmapBranch
    SLeaf -> coerceFmapLeaf
  {-# INLINE fmap #-}

instance (SingI es, Monad m) => Applicative (Eff es m) where
  pure = case sing @es of
    SEmpty -> coercePureEmpty
    SLeaf -> coercePureLeaf
    SBranch -> coercePureBranch
  {-# INLINE pure #-}

  (<*>) = case sing @es of
    SEmpty -> coerceAppEmpty
    SLeaf -> coerceAppLeaf
    SBranch -> coerceAppBranch
  {-# INLINE (<*>) #-}

  (*>) = case sing @es of
    SEmpty -> coerceAndThenEmpty
    SLeaf -> coerceAndThenLeaf
    SBranch -> coerceAndThenBranch
  {-# INLINE (*>) #-}

instance (SingI es, Monad m) => Monad (Eff es m) where
  (>>=) = case sing @es of
    SEmpty -> coerceBindEmpty
    SLeaf -> coerceBindLeaf
    SBranch -> coerceBindBranch
  {-# INLINE (>>=) #-}

main :: IO ()
main = pure ()
