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

import Control.Monad.Morph (hoist)
import Control.Monad.Trans (MonadTrans (lift))
import Control.Monad.Trans.State.Strict as State
import Data.Kind (Type)

data Rose a = Branch (Rose a) (Rose a) | Leaf a | Empty

data SRose i where
  SBranch :: (SingI i1, SingI i2) => SRose (Branch i1 i2)
  SLeaf :: (MonadTrans t) => SRose (Leaf t)
  SEmpty :: SRose Empty

class SingI i where
  sing :: SRose i

instance (MonadTrans t) => SingI (Leaf t) where
  sing = SLeaf

instance (SingI t1, SingI t2) => SingI (Branch t1 t2) where
  sing = SBranch

instance SingI Empty where
  sing = SEmpty

type (:&) = 'Branch

type Effect = (Type -> Type) -> Type -> Type

data Eff (es :: Rose Effect) m a where
  EffEmpty :: m a -> Eff Empty m a
  EffLeaf :: t m a -> Eff (Leaf t) m a
  EffBranch :: Eff s1 (Eff s2 m) a -> Eff (Branch s1 s2) m a

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
    SEmpty -> \(EffEmpty m) f -> f =<< EffEmpty m
    SLeaf -> \(EffLeaf m) f -> f =<< EffLeaf m
    SBranch -> \(EffBranch m) f -> f =<< EffBranch m

instance (SingI es) => MonadTrans (Eff es) where
  lift = case sing @es of
    SEmpty -> EffEmpty
    SLeaf -> EffLeaf . lift
    SBranch -> EffBranch . lift . lift

handleState ::
  (SingI effs, Monad m) =>
  s ->
  ( ( forall m' a'.
      (Monad m') =>
      StateT s m' a' ->
      Eff (Leaf (StateT s) :& effs) m' a'
    ) ->
    Eff (Leaf (StateT s) :& effs) m a
  ) ->
  Eff effs m a
handleState s f = case f (EffBranch . EffLeaf . hoist lift) of
  EffBranch (EffLeaf m) -> evalStateT m s
