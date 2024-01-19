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
{-# LANGUAGE TypeOperators #-}

module RoseMTL where

import qualified Control.Monad.State.Strict as TransState
import Control.Monad.Trans (MonadTrans)
import Control.Monad.Trans.State.Strict (StateT)
import qualified Control.Monad.Trans.State.Strict as State
import Data.Coerce (coerce)
import Data.Foldable (for_)
import Data.Functor.Identity (Identity (Identity, runIdentity))
import Data.Kind (Type)
import Prelude hiding (read)

data Effects = Branch Effects Effects | Leaf ((Type -> Type) -> Type -> Type) | Empty

data SEffects i where
  SBranch :: (SingI i1, SingI i2) => SEffects (Branch i1 i2)
  SLeaf :: (MonadTrans t) => SEffects (Leaf t)
  SEmpty :: SEffects Empty

class SingI i where
  sing :: SEffects i

instance (MonadTrans t) => SingI (Leaf t) where
  sing = SLeaf

instance (SingI t1, SingI t2) => SingI (Branch t1 t2) where
  sing = SBranch

instance SingI Empty where
  sing = SEmpty

type (:&) = 'Branch

newtype Eff es m a = MkEff {unMkEff :: EffF es m a}

type family EffF (es :: Effects) m where
  EffF Empty m = m
  EffF (Leaf t) m = t m
  EffF (Branch s1 s2) m = Eff s1 (Eff s2 m)

runEffPure :: Eff Empty Identity a -> a
runEffPure = coerce
{-# INLINE runEffPure #-}

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

instance (SingI es, Monad m) => Functor (Eff es m) where
  fmap = case sing @es of
    SEmpty -> coerceFmapEmpty
    SBranch -> coerceFmapBranch
    SLeaf -> coerceFmapLeaf
  {-# INLINE fmap #-}

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

coerceBindAndThenEmpty ::
  forall m a b. (Monad m) => Eff Empty m a -> Eff Empty m b -> Eff Empty m b
coerceBindAndThenEmpty = coerce ((>>) :: m a -> m b -> m b)

coerceBindAndThenLeaf ::
  forall t m a b.
  (MonadTrans t, Monad m) =>
  Eff (Leaf t) m a ->
  Eff (Leaf t) m b ->
  Eff (Leaf t) m b
coerceBindAndThenLeaf = coerce ((>>) :: t m a -> t m b -> t m b)

coerceBindAndThenBranch ::
  forall s1 s2 m a b.
  (SingI s1, SingI s2, Monad m) =>
  Eff (Branch s1 s2) m a ->
  Eff (Branch s1 s2) m b ->
  Eff (Branch s1 s2) m b
coerceBindAndThenBranch =
  coerce
    ( (>>) ::
        Eff s1 (Eff s2 m) a ->
        Eff s1 (Eff s2 m) b ->
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

instance (SingI es, Monad m) => Applicative (Eff es m) where
  pure = case sing @es of
    SEmpty -> coercePureEmpty
    SLeaf -> coercePureLeaf
    SBranch -> coercePureBranch
  {-# INLINE pure #-}

  (<*>) = case sing @es of
    SEmpty -> \(MkEff f) (MkEff g) -> coerce (f <*> g)
    SLeaf -> \(MkEff f) (MkEff g) -> coerce (f <*> g)
    SBranch -> \(MkEff f) (MkEff g) -> coerce (f <*> g)
  {-# INLINE (<*>) #-}

  (*>) = case sing @es of
    SEmpty -> coerceAndThenEmpty
    SLeaf -> coerceAndThenLeaf
    SBranch -> coerceAndThenBranch
  {-# INLINE (*>) #-}

instance (SingI es, Monad m) => Monad (Eff es m) where
  (>>) = case sing @es of
    SEmpty -> coerceBindAndThenEmpty
    SLeaf -> coerceBindAndThenLeaf
    SBranch -> coerceBindAndThenBranch

  (>>=) = case sing @es of
    SEmpty -> coerceBindEmpty
    SLeaf -> coerceBindLeaf
    SBranch -> coerceBindBranch
  {-# INLINE (>>=) #-}

type HandlerNoArgs s effs m a r =
  Eff (s :& effs) m a ->
  Eff effs m r

handleAnyNoArgs ::
  (MonadTrans t) =>
  (t (Eff effs m) a -> Eff effs m r) ->
  HandlerNoArgs (Leaf t) effs m a r
handleAnyNoArgs = coerce
{-# INLINE handleAnyNoArgs #-}

runStateNoArgs ::
  (SingI effs, Monad m) =>
  s ->
  HandlerNoArgs (Leaf (StateT s)) effs m a (a, s)
runStateNoArgs s = handleAnyNoArgs (flip State.runStateT s)
{-# INLINE runStateNoArgs #-}

handleStateNoArgs ::
  (SingI effs, Monad m) =>
  s ->
  HandlerNoArgs (Leaf (StateT s)) effs m a a
handleStateNoArgs s f = fmap fst (runStateNoArgs s f)
{-# INLINE handleStateNoArgs #-}

myfor :: (Applicative f) => Int -> (Int -> f a) -> f ()
myfor 0 _ = pure ()
myfor n b = b n *> myfor (n - 1) b

mySum :: Int
mySum = runEffPure
  $ ( ( coerce ::
          (StateT Int (Eff Empty Identity) Int -> Eff Empty Identity Int) ->
          Eff (Leaf (StateT Int) :& Empty) Identity Int ->
          Eff Empty Identity Int
      )
        (flip State.evalStateT (0 :: Int))
    )
  $ MkEff
  $ do
    MkEff $ do
      -- Getting rid of this "pure" leads to less good code!
      pure ()
      for_ [1 :: Int .. 10] $ \i -> do
        do
          s <- State.get
          State.put $! s + i
    MkEff $ do
      State.get

mySumMTL :: Int
mySumMTL = runIdentity $ flip State.evalStateT 0 $ do
  for_ [1 :: Int .. 10] $ \i -> do
    s <- TransState.get
    TransState.put $! s + i
  TransState.get

newtype N m a = N {unN :: m a}
  deriving newtype (Functor, Applicative, Monad)

newtype M t m a = M {unM :: t m a}
  deriving newtype (Functor, Applicative, Monad)

mySumN :: Int
mySumN = runIdentity $ flip State.evalStateT 0 $ unN $ unM $ do
  M $ do
    N $ do
      for_ [1 :: Int .. 10] $ \i -> do
        do
          s <- TransState.get
          TransState.put $! s + i
    N $ do
      TransState.get
