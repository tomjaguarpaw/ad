{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

module L where

import Control.Monad.Trans.Class (lift)
import qualified Control.Monad.Trans.State as State
import Data.Kind (Constraint, Type)
import qualified Data.Map.Strict as Map

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

type SLType' (t :: LType p) = SLType p t

type SLType :: forall (p :: Polarity) -> LType p -> Type
data SLType p a where
  STensor ::
    SLType' a ->
    SLType' b ->
    SLType' (a `Tensor` b)
  SDown :: SLType' a -> SLType' (Down a)
  SBottom :: SLType' Bottom

class KnownLType' (a :: LType p) where
  know :: SLType p a

instance (KnownLType' a, KnownLType' b) => KnownLType' (a `Tensor` b) where
  know = STensor know know

instance KnownLType' Bottom where
  know = SBottom

instance (KnownLType' a) => KnownLType' (Down a) where
  know = SDown know

type Perp :: forall (p :: Polarity). LType p -> LType (Flip p)
type family Perp t = t' {- can't do | t' -> t -} where
  Perp (TyVar a) = TyVarPerp a
  Perp (TyVar a) = TyVarPerp' a
  Perp (TyVarPerp a) = TyVar a
  Perp (TyVarPerp' a) = TyVar a
  Perp (a `Tensor` b) = Perp a `Dna` Perp b
  Perp One = Bottom
  Perp (a `Plus` b) = Perp a `And` Perp b
  Perp Zero = Top
  Perp (Bang a) = WhyNot (Perp a)
  Perp (Down a) = Up (Perp a)
  Perp (a `Dna` b) = Perp a `Tensor` Perp b
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
  -- Not sure how to stop the computation
  Stop :: (KnownLType' a) => Term p a

deriving instance Show (Term p t)

data Computation where
  Computation :: Term Negative (Perp a) -> Term Positive a -> Computation

deriving instance Show Computation

showTerm :: Term p t -> String
showTerm = \case
  Var v -> v
  Mu v c -> "μ" ++ v ++ ". " ++ showComputation c
  Pair t1 t2 -> "(" ++ showTerm t1 ++ ", " ++ showTerm t2 ++ ")"
  MuPair v1 v2 c -> "μ(" ++ v1 ++ ", " ++ v2 ++ "). " ++ showComputation c
  Unit -> "()"
  MuUnit {} -> error "MuUnit"
  OneDot {} -> error "OneDot"
  TwoDot {} -> error "TwoDot"
  MuDot {} -> error "MuDot"
  EmptyCase {} -> error "EmptyCase"
  Return t -> "⇑" ++ showTerm t
  MuReturn v c -> "μ⇑" ++ v ++ "." ++ showComputation c
  Stop -> "Stop"

showComputation :: Computation -> String
showComputation (Computation t1 t2) =
  "〈" ++ showTerm t1 ++ "|" ++ showTerm t2 ++ "〉"

type Lolly :: LType Positive -> LType Negative -> LType Negative
type Lolly a b = Perp a `Dna` b

-- To be improved ...
type KnownLType :: forall (p :: Polarity). LType p -> Constraint
type family KnownLType t where
  KnownLType (t :: LType Positive) = t ~ Perp (Perp t)
  KnownLType (t :: LType Negative) = t ~ Perp (Perp t)

type M = State.State Int

runM :: M a -> a
runM = flip State.evalState 0

fresh :: String -> M (VarId a)
fresh s = do
  i <- State.get
  State.modify' (+ 1)
  pure (s ++ show i)

-- p5
lam ::
  forall a b.
  (KnownLType b) =>
  VarId a ->
  Term' b ->
  M (Term' (a `Lolly` b))
-- fixme: fresh variable
lam x t = do
  a <- fresh "α"
  let comp :: Computation
      comp = Computation t (Var @(Perp b) a)
  pure (MuPair @a @(Perp b) x a comp)

type Term' (t :: LType p) = Term p t

apply ::
  forall a b.
  (KnownLType b) =>
  Term' (a `Lolly` b) ->
  Term' a ->
  M (Term Negative b)
apply t u = do
  alpha <- fresh "α"
  let pair :: Term' (a `Tensor` Perp b)
      pair = u `Pair` Var alpha
  pure (Mu @(Perp b) alpha (Computation t pair))

-- p20
thunk ::
  forall n.
  (KnownLType n) =>
  Term Negative n ->
  M (Term Positive (Down n))
thunk t = do
  alpha <- fresh "α"
  pure (MuReturn @(Perp n) alpha (Computation t (Var @(Perp n) alpha)))

-- p22
to ::
  forall a n.
  (KnownLType a) =>
  (KnownLType n) =>
  Term' (Up a) ->
  VarId a ->
  M
    ( Term Negative n ->
      Term' n
    )
t `to` x = do
  alpha <- fresh "α"
  pure $ \u ->
    let comp1 = Computation u (Var @(Perp n) alpha)
        comp2 = Computation t (MuReturn @a x comp1)
     in Mu @(Perp n) alpha comp2

-- p22
force ::
  forall n.
  (KnownLType n) =>
  Term Positive (Down n) ->
  M (Term Negative n)
force t = do
  alpha <- fresh "α"
  let returnAlpha :: Term Negative (Up (Perp n))
      returnAlpha = Return (Var alpha)
  pure (Mu @(Perp n) alpha (Computation returnAlpha t))

-- p23
cbvLam ::
  forall a b.
  (KnownLType b) =>
  (KnownLType (a `Lolly` Up b)) =>
  VarId a ->
  Term' (CBVType b) ->
  M (Term' (CBVType (a `CBVLolly` b)))
cbvLam x t =
  Return <$> (thunk =<< lam @a x t)

-- p21
cbvApply ::
  forall a b.
  (KnownLType a) =>
  (KnownLType b) =>
  (KnownLType (a `Lolly` Up b)) =>
  Term Negative (CBVType (a `CBVLolly` b)) ->
  Term Negative (CBVType a) ->
  M (Term' (CBVType b))
cbvApply t u = do
  x <- fresh "x"
  f <- fresh "f"
  (u `to` x) <*> ((t `to` f) <*> (do f' <- force (Var f); apply f' (Var @a x)))

cbvVar :: VarId a -> Term 'Negative ('Up a)
cbvVar = Return . Var

type CBVType a = Up a

type CBVLolly a b = Down (a `Lolly` Up b)

exampleTerm ::
  forall a0 a1 b.
  (KnownLType (a0 :: LType Positive)) =>
  (KnownLType (a1 :: LType Positive)) =>
  (KnownLType b) =>
  M (Term' (CBVType b))
exampleTerm = do
  x <- fresh "x"
  y <- fresh "y"
  one <- fresh "one"
  two <- fresh "two"
  minus <- fresh "sub"

  inner <-
    cbvApply <$> cbvApply (cbvVar minus) (cbvVar @a0 x) <*> pure (cbvVar @a1 y)

  lam_ <- cbvLam @a0 x =<< (cbvLam @a1 y =<< inner)

  applied <- cbvApply <$> cbvApply lam_ (cbvVar @a0 one) <*> pure (cbvVar @a1 two)
  applied

data TypedTerm p where
  TypedTerm ::
    forall (p :: Polarity) (t :: LType p).
    SLType p t ->
    Term p t ->
    TypedTerm p

-- This is silly and expensive.  We should store the type with each
-- constructor.
typedTerm :: Term p t -> TypedTerm p
typedTerm = \case
  Var {} -> error "Var"
  Mu {} -> error "Mu"
  Pair {} -> error "Pair"
  MuPair {} -> error "MuPair"
  Unit {} -> error "Unit"
  MuUnit {} -> error "MuUnit"
  OneDot {} -> error "OneDot"
  TwoDot {} -> error "TwoDot"
  MuDot {} -> error "MuDot"
  EmptyCase {} -> error "EmptCase"
  Return {} -> error "Retur"
  MuReturn {} -> error "MuReturn"

type Subst = Map.Map String (TypedTerm Positive)

-- p21
-- These are the opposite way round!
step :: (Monad m) => Computation -> State.StateT Subst m (Maybe Computation)
step (Computation (Mu x c) t) = do
  State.modify' (Map.insert x (typedTerm t))
  pure (Just c)
step c = error (show c)

type TermType = CBVType One

example :: IO ()
example = do
  let term :: Term' TermType
      term = runM (exampleTerm @One @One @One)

  putStrLn (showTerm term)

  let loop c =
        step c >>= \case
          Nothing -> pure ()
          Just c' -> do
            lift (putStrLn (showComputation c'))
            loop c'

  flip
    State.evalStateT
    Map.empty
    -- This type argument is annoying
    (loop (Computation @(Perp TermType) term Stop))
