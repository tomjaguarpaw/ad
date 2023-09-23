{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

module L where

import Data.Kind (Constraint, Type)

data Polarity = Positive | Negative

type Flip :: Polarity -> Polarity
type family Flip a = f | f -> a where
  Flip Positive = Negative
  Flip Negative = Positive

type TyVarId :: Polarity -> Type
type TyVarId a = String

type LType :: Polarity -> Type
data LType p where
  TyVar :: TyVarId p -> LType p
  -- If we use Flip to make just one constructor then we can't write
  -- the Perp type family :(
  TyVarPerp :: TyVarId Positive -> LType Negative
  TyVarPerp' :: TyVarId Negative -> LType Positive
  Tensor :: LType Positive -> LType Positive -> LType Positive
  One :: LType Positive
  Plus :: LType Positive -> LType Positive -> LType Positive
  Zero :: LType Positive
  Bang :: LType Positive -> LType Positive
  Down :: LType Negative -> LType Positive
  Dna :: LType Negative -> LType Negative -> LType Negative
  Bottom :: LType Negative
  And :: LType Negative -> LType Negative -> LType Negative
  Top :: LType Negative
  WhyNot :: LType Negative -> LType Negative
  Up :: LType Positive -> LType Negative

type Perp :: forall (p :: Polarity). LType p -> LType (Flip p)
type family Perp t = t' {- can't do | t' -> t -} where
  Perp (TyVar a) = TyVarPerp a
  Perp (TyVarPerp a) = TyVar a
  Perp (TyVarPerp' a) = TyVar a
  Perp (a `Tensor` b) = Perp a `Dna` Perp b
  Perp One = Bottom
  Perp (a `Plus` b) = Perp a `And` Perp b
  Perp Zero = Top
  Perp (Bang a) = WhyNot (Perp a)
  Perp (Down a) = Up (Perp a)
  Perp Bottom = One
  Perp (a `And` b) = Perp a `Plus` Perp b
  Perp Top = Zero
  Perp (WhyNot a) = Bang (Perp a)
  Perp (Up a) = Down (Perp a)

type VarId :: LType Positive -> Type
type VarId a = String

type Term :: forall (p :: Polarity) -> LType p -> Type
data Term p t where
  Var :: VarId a -> Term Positive a
  Mu :: VarId a -> Computation -> Term Negative (Perp a)
  Pair :: Term Positive a -> Term Positive b -> Term Positive (a `Tensor` b)
  MuPair ::
    VarId a ->
    VarId b ->
    Computation ->
    Term Negative (Perp a `Dna` Perp b)
  Unit :: Term Positive One
  MuUnit :: Computation -> Term Negative Bottom
  OneDot :: Term Positive a -> Term Positive (a `Plus` b)
  TwoDot :: Term Positive b -> Term Positive (a `Plus` b)
  MuDot ::
    VarId a ->
    Computation ->
    VarId b ->
    Computation ->
    Term Negative (Perp a `And` Perp b)
  EmptyCase :: Term Negative Top
  Return :: Term Positive a -> Term Negative (Up a)
  MuReturn :: VarId a -> Computation -> Term Positive (Down (Perp a))

data Computation where
  Computation :: Term Negative (Perp a) -> Term Positive a -> Computation

type Lolly :: LType Positive -> LType Negative -> LType Negative
type Lolly a b = Perp a `Dna` b

-- To be improved ...
type KnownLType :: forall (p :: Polarity). LType p -> Constraint
type family KnownLType t where
  KnownLType (t :: LType Positive) = t ~ Perp (Perp t)
  KnownLType (t :: LType Negative) = t ~ Perp (Perp t)

-- p5
lam ::
  forall a b.
  (KnownLType b) =>
  VarId a ->
  Term' b ->
  Term' (a `Lolly` b)
-- fixme: fresh variable
lam x t = MuPair @a @(Perp b) x a comp
  where
    vara :: Term Positive (Perp b)
    vara = Var a

    a :: VarId a
    a = "alpha"

    comp :: Computation
    comp = Computation t vara

type Term' (t :: LType p) = Term p t

apply ::
  forall a b.
  (KnownLType b) =>
  Term' (a `Lolly` b) ->
  Term' a ->
  Term Negative b
apply t u =
  Mu @(Perp b) alpha (Computation t pair)
  where
    alpha = "alpha1"

    pair :: Term' (a `Tensor` Perp b)
    pair = u `Pair` Var alpha

-- p20
thunk ::
  forall n.
  (KnownLType n) =>
  Term Negative n ->
  Term Positive (Down n)
thunk t = MuReturn @(Perp n) alpha (Computation t (Var @(Perp n) alpha))
  where
    alpha :: VarId (Perp n)
    alpha = "alpha2"

-- p22
to ::
  forall a n.
  (KnownLType a) =>
  (KnownLType n) =>
  Term' (Up a) ->
  VarId a ->
  Term Negative n ->
  Term' n
(t `to` x) u = Mu @(Perp n) alpha comp2
  where
    alpha = "alpha3"
    comp1 = Computation u (Var @(Perp n) alpha)
    comp2 = Computation t (MuReturn @a x comp1)

-- p22
force ::
  forall n.
  (KnownLType n) =>
  Term Positive (Down n) ->
  Term Negative n
force t = Mu @(Perp n) alpha (Computation returnAlpha t)
  where
    alpha = "alpha"

    returnAlpha :: Term Negative (Up (Perp n))
    returnAlpha = Return (Var alpha)

-- p23
cbvLam ::
  forall a b.
  (KnownLType b) =>
  (KnownLType (Perp a `Dna` Up b)) =>
  VarId a ->
  Term Negative (Up b) ->
  Term Negative (Up (Down (a `Lolly` Up b)))
cbvLam x t = Return (thunk @(a `Lolly` Up b) (lam @a x t))

cbaApply ::
  forall a b.
  (KnownLType a) =>
  (KnownLType b) =>
  (KnownLType (Perp a `Dna` Up b)) =>
  Term Negative (Up (Down (a `Lolly` Up b))) ->
  Term Negative (Up a) ->
  Term Negative (Up b)
cbaApply t u =
  u `to` x $ t `to` f $ force (Var f) `apply` Var @a x
  where
    x = "x"
    f = "f"
