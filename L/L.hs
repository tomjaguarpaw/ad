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
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

module L where

import Data.Kind (Type)

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
  Computation :: Term Positive a -> Term Negative (Perp a) -> Computation

type Lolly :: LType Positive -> LType Negative -> LType Negative

type Lolly a b = Perp a `Dna` b

lam ::
  forall a b b'.
  b ~ Perp b' =>
  VarId a ->
  Term' b ->
  Term' (a `Lolly` b)
-- fixme: fresh variable
lam x t = MuPair @a @b' x a comp
  where
    vara :: Term Positive b'
    vara = Var a

    a :: VarId a
    a = "alpha"

    comp :: Computation
    comp = Computation vara t

type Term' (t :: LType p) = Term p t

apply ::
  forall a b b'.
  (b ~ Perp b', Perp b ~ b') =>
  Term' (a `Lolly` b) ->
  Term' a ->
  Term Negative b
apply t u =
  -- < pair | t> is the opposite way round from p5
  Mu @b' alpha (Computation pair t)
  where
    alpha = "alpha1"

    pair :: Term' (a `Tensor` Perp b)
    pair = u `Pair` Var alpha

-- p20
thunk ::
  forall n n'.
  n' ~ Perp n =>
  n ~ Perp n' =>
  Term Negative n ->
  Term Positive (Down n)
thunk t = MuReturn @n' alpha (Computation @n' (Var alpha) t)
  where
    alpha :: VarId n'
    alpha = "alpha2"
