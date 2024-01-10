{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE UnliftedNewtypes #-}

module RoseMTL where

import Control.Monad.Morph (MFunctor, hoist)
import Control.Monad.Trans (MonadTrans (lift))
import Control.Monad.Trans.State.Strict (StateT)
import qualified Control.Monad.Trans.State.Strict as State
import Data.Foldable (for_)
import Data.Functor.Identity (Identity (runIdentity))
import Data.Kind (Type)
import Prelude hiding (read)

data Rose a = Branch (Rose a) (Rose a) | Leaf a | Empty

data SRose i where
  SBranch :: (SingI i1, SingI i2) => SRose (Branch i1 i2)
  SLeaf :: (MonadTrans t, MFunctor t) => SRose (Leaf t)
  SEmpty :: SRose Empty

class SingI i where
  sing :: SRose i

instance (MonadTrans t, MFunctor t) => SingI (Leaf t) where
  sing = SLeaf

instance (SingI t1, SingI t2) => SingI (Branch t1 t2) where
  sing = SBranch

instance SingI Empty where
  sing = SEmpty

type (:&) = 'Branch

type Effect = (Type -> Type) -> Type -> Type

class (a :: Rose Effect) :> (b :: Rose Effect) where
  embed :: (Monad m) => Eff a m r -> Eff b m r

instance {-# INCOHERENT #-} e :> e where
  embed = id

instance (SingI x, SingI es, (e :> es)) => e :> (x :& es) where
  embed = EffBranch . lift . embed

-- Do we want this?
-- instance {-# incoherent #-} (e :> es) => (e' :& e) :> (e' :> es)

-- This seems a bit wobbly
instance {-# INCOHERENT #-} (SingI e, SingI es) => e :> (e :& es) where
  embed = EffBranch . hoist lift

embed' :: forall a b m r. (a :> b, Monad m) => Eff a m r -> Eff b m r
embed' = embed

data Eff (es :: Rose Effect) m a where
  EffEmpty :: m a -> Eff Empty m a
  EffLeaf :: t m a -> Eff (Leaf t) m a
  EffBranch :: Eff s1 (Eff s2 m) a -> Eff (Branch s1 s2) m a

runEffPure :: Eff Empty Identity a -> a
runEffPure = \case
  EffEmpty ma -> runIdentity ma

instance (SingI es, Monad m) => Functor (Eff es m) where
  fmap f = case sing @es of
    SEmpty -> \(EffEmpty ma) -> EffEmpty (fmap f ma)
    SBranch -> \(EffBranch ema) -> EffBranch (fmap f ema)
    SLeaf -> \(EffLeaf tma) -> EffLeaf (fmap f tma)

instance (SingI es, Monad m) => Applicative (Eff es m) where
  pure = case sing @es of
    SEmpty -> EffEmpty . pure
    SLeaf -> EffLeaf . lift . pure
    SBranch -> EffBranch . lift . pure

  (<*>) = case sing @es of
    SEmpty -> \(EffEmpty f) (EffEmpty g) -> EffEmpty (f <*> g)
    SLeaf -> \(EffLeaf f) (EffLeaf g) -> EffLeaf (f <*> g)
    SBranch -> \(EffBranch f) (EffBranch g) -> EffBranch (f <*> g)

instance (SingI es, Monad m) => Monad (Eff es m) where
  (>>=) = case sing @es of
    SEmpty -> \(EffEmpty m) f -> EffEmpty $ do
      m' <- m
      case f m' of EffEmpty m'' -> m''
    SLeaf -> \(EffLeaf m) f -> EffLeaf $ do
      m' <- m
      case f m' of EffLeaf m'' -> m''
    SBranch -> \(EffBranch m) f -> EffBranch $ do
      m' <- m
      case f m' of EffBranch m'' -> m''

instance (SingI es) => MonadTrans (Eff es) where
  lift = case sing @es of
    SEmpty -> EffEmpty
    SLeaf -> EffLeaf . lift
    SBranch -> EffBranch . lift . lift

instance (SingI es) => MFunctor (Eff es) where
  hoist f = case sing @es of
    SEmpty -> \(EffEmpty m) -> EffEmpty (f m)
    SLeaf -> \(EffLeaf m) -> EffLeaf (hoist f m)
    SBranch -> \(EffBranch m) -> EffBranch (hoist (hoist f) m)

data State s st where
  MkState ::
    ( forall m' a' effs.
      (Leaf (StateT s) :> effs) =>
      (SingI effs) =>
      (Monad m') =>
      StateT s m' a' ->
      Eff effs m' a'
    ) ->
    State s (Leaf (StateT s))

handleState ::
  (SingI effs, Monad m) =>
  s ->
  (forall st. SingI st => State s st -> Eff (st :& effs) m a) ->
  Eff effs m a
handleState s f = case f (MkState (embed . EffLeaf)) of
  EffBranch (EffLeaf m) -> State.evalStateT m s

read ::
  (SingI effs, st :> effs, Monad m) => State s st -> Eff effs m s
read (MkState r) = r State.get

write :: (st :> effs, SingI effs, Monad m) => State s st -> s -> Eff effs m ()
write (MkState r) s = r (State.put s)

modify ::
  (Monad m, SingI effs, st :> effs) => State s st -> (s -> s) -> Eff effs m ()
modify state f = do
  !s <- read state
  write state (f s)

examplePure :: (SingI effs, Monad m) => Eff effs m ()
examplePure = pure ()

exampleRead :: (SingI effs, Monad m) => Eff effs m ()
exampleRead =
  handleState () $ \st -> read st

exampleWrite :: (SingI effs, Monad m) => Eff effs m (Int, Int)
exampleWrite =
  handleState 0 $ \st -> do
    handleState 100 $ \st2 -> do
      modify st (+ 1)
      modify st2 (* 2)
      (,) <$> read st <*> read st2

exampleParity :: (SingI effs, Monad m) => Eff effs m (Int, Int)
exampleParity =
  handleState 0 $ \evens -> do
    handleState 0 $ \odds -> do
      for_ [1 :: Int .. 10] $ \i -> do
        ( if even i
            then modify odds
            else modify evens
          )
          (+ 1)

      e <- read evens
      o <- read odds

      pure (e, o)
