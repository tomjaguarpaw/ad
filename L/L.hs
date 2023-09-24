{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

{- HLINT ignore "Use join" -}
{- HLINT ignore "Use forM_" -}
{- HLINT ignore "Redundant flip" -}

module L where

import Control.Monad.Trans.Class (lift)
import qualified Control.Monad.Trans.State as State
import Data.Kind (Constraint, Type)
import qualified Data.Map.Strict as Map
import Data.Type.Equality (type (~~))

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
  LInt :: LType Positive
  PerpLInt :: LType Negative
  Heap :: LType Positive -> LType Positive
  PerpHeap :: LType Negative -> LType Negative

type SLType' (t :: LType p) = SLType p t

type SLType :: forall (p :: Polarity) -> LType p -> Type
data SLType p a where
  STensor ::
    SLType' a ->
    SLType' b ->
    SLType' (a `Tensor` b)
  SDna ::
    SLType' a ->
    SLType' b ->
    SLType' (a `Dna` b)
  SDown :: SLType' a -> SLType' (Down a)
  SUp :: SLType' a -> SLType' (Up a)
  SBottom :: SLType' Bottom
  SOne :: SLType' One
  SLInt :: SLType' LInt
  SPerpLInt :: SLType' PerpLInt
  SHeap :: SLType' a -> SLType' (Heap a)
  SPerpHeap :: SLType' a -> SLType' (PerpHeap a)

deriving instance Show (SLType p t)

data Dict c where
  Dict :: (c) => Dict c

perpSLType :: SLType p t -> SLType (Flip p) (Perp t)
perpSLType = \case
  STensor a b -> SDna (perpSLType a) (perpSLType b)
  SDna a b -> STensor (perpSLType a) (perpSLType b)
  SDown a -> SUp (perpSLType a)
  SUp a -> SDown (perpSLType a)
  SBottom -> SOne
  SOne -> SBottom
  SLInt -> SPerpLInt
  SPerpLInt -> SLInt
  SHeap a -> SPerpHeap (perpSLType a)
  SPerpHeap a -> SHeap (perpSLType a)

-- ~~ is annoying here
--
-- This not complete!
eqSLType :: SLType p t -> SLType p' t' -> Maybe (Dict (p ~ p', t ~~ t'))
eqSLType (STensor a b) (STensor a' b') = do
  Dict <- eqSLType a a'
  Dict <- eqSLType b b'
  pure Dict
eqSLType STensor {} _ = Nothing
eqSLType (SDna a b) (SDna a' b') = do
  Dict <- eqSLType a a'
  Dict <- eqSLType b b'
  pure Dict
eqSLType SDna {} _ = Nothing
eqSLType (SDown a) (SDown a') = do
  Dict <- eqSLType a a'
  pure Dict
eqSLType SDown {} _ = Nothing
eqSLType (SUp a) (SUp a') = do
  Dict <- eqSLType a a'
  pure Dict
eqSLType SUp {} _ = Nothing
eqSLType SBottom SBottom = pure Dict
eqSLType SBottom {} _ = Nothing
eqSLType SOne SOne = pure Dict
eqSLType SOne {} _ = Nothing
eqSLType SLInt SLInt = pure Dict
eqSLType SLInt {} _ = Nothing
eqSLType SPerpLInt SPerpLInt = pure Dict
eqSLType SPerpLInt {} _ = Nothing
eqSLType SHeap {} _ = error "Heap not yet supported"
eqSLType SPerpHeap {} _ = error "Heap not yet supported"

class KnownLType' (a :: LType p) where
  know :: SLType p a

instance (KnownLType' a, KnownLType' b) => KnownLType' (a `Tensor` b) where
  know = STensor know know

instance (KnownLType' a, KnownLType' b) => KnownLType' (a `Dna` b) where
  know = SDna know know

instance KnownLType' One where
  know = SOne

instance KnownLType' Bottom where
  know = SBottom

instance (KnownLType' a) => KnownLType' (Down a) where
  know = SDown know

instance (KnownLType' a) => KnownLType' (Up a) where
  know = SUp know

instance KnownLType' LInt where
  know = SLInt

instance KnownLType' PerpLInt where
  know = SPerpLInt

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
  Perp LInt = PerpLInt
  Perp PerpLInt = LInt
  Perp (Heap a) = PerpHeap (Perp a)
  Perp (PerpHeap a) = Heap (Perp a)

type VarId :: LType Positive -> Type
type VarId a = String

type Term :: forall (p :: Polarity) -> LType p -> Type
data Term p t where
  Var :: (KnownLType' a) => VarId a -> Term Positive a
  Mu :: VarId a -> Computation -> Term Negative (Perp a)
  Pair ::
    (KnownLType' (a `Tensor` b)) =>
    (Term Positive a, Term Positive b) ->
    Term Positive (a `Tensor` b)
  MuPair ::
    forall a b.
    (KnownLType' (Perp a `Dna` Perp b)) =>
    (VarId a, VarId b) ->
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
  Return ::
    (KnownLType' a) =>
    Term Positive a ->
    Term Negative (Up a)
  MuReturn ::
    forall a.
    (KnownLType' a, KnownLType' (Perp a)) =>
    VarId a ->
    Computation ->
    Term Positive (Down (Perp a))
  -- Not sure how to stop the computation
  Debug :: (KnownLType' a) => String -> Term p a
  Stop :: (KnownLType' a) => Term Negative a
  Sub :: Term Negative (Perp LInt) -> Term Negative (Perp (LInt `Tensor` LInt))
  IntLit :: Int -> Term Positive LInt

deriving instance Show (Term p t)

data Computation where
  Computation :: Term Negative (Perp a) -> Term Positive a -> Computation

deriving instance Show Computation

showTerm :: Term p t -> String
showTerm = \case
  Var v -> v
  Mu v c -> "μ" ++ v ++ ". " ++ showComputation c
  Pair (t1, t2) -> "(" ++ showTerm t1 ++ ", " ++ showTerm t2 ++ ")"
  MuPair (v1, v2) c -> "μ(" ++ v1 ++ ", " ++ v2 ++ "). " ++ showComputation c
  Unit -> "()"
  MuUnit {} -> error "MuUnit"
  OneDot {} -> error "OneDot"
  TwoDot {} -> error "TwoDot"
  MuDot {} -> error "MuDot"
  EmptyCase {} -> error "EmptyCase"
  Return t -> "⇑" ++ showTerm t
  MuReturn v c -> "μ⇑" ++ v ++ "." ++ showComputation c
  Debug s -> "Debug " ++ s
  Stop -> "Stop"
  Sub c -> "Sub. " ++ showTerm c
  IntLit i -> show i

showComputation :: Computation -> String
showComputation (Computation t1 t2) =
  "〈" ++ showTerm t1 ++ "|" ++ showTerm t2 ++ "〉"

type Lolly :: LType Positive -> LType Negative -> LType Negative
type Lolly a b = Perp a `Dna` b

-- To be improved ...
type KnownLType :: forall (p :: Polarity). LType p -> Constraint
type family KnownLType t where
  KnownLType (t :: LType Positive) = (t ~ Perp (Perp t), KnownLType' t, KnownLType' (Perp t))
  KnownLType (t :: LType Negative) = (t ~ Perp (Perp t), KnownLType' t, KnownLType' (Perp t))

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
  (KnownLType a) =>
  (KnownLType b) =>
  VarId a ->
  Term' b ->
  M (Term' (a `Lolly` b))
-- fixme: fresh variable
lam x t = do
  a <- fresh "α"
  let comp :: Computation
      comp = Computation t (Var @(Perp b) a)
  pure (MuPair @a @(Perp b) (x, a) comp)

type Term' (t :: LType p) = Term p t

apply ::
  forall a b.
  (KnownLType a) =>
  (KnownLType b) =>
  Term' (a `Lolly` b) ->
  Term' a ->
  M (Term Negative b)
apply t u = do
  alpha <- fresh "α"
  let pair :: Term' (a `Tensor` Perp b)
      pair = Pair (u, Var alpha)
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
  (KnownLType a) =>
  (KnownLType b) =>
  (KnownLType (a `Lolly` CBVType b)) =>
  VarId a ->
  Term' (CBVType b) ->
  M (Term' (CBVType (a `CBVLolly` b)))
cbvLam x t =
  Return <$> (thunk =<< lam @a x t)

-- p23
cbvApply ::
  forall a b.
  (KnownLType a) =>
  (KnownLType b) =>
  Term Negative (CBVType (a `CBVLolly` b)) ->
  Term Negative (CBVType a) ->
  M (Term' (CBVType b))
cbvApply t u = do
  x <- fresh "x"
  f <- fresh "f"
  (u `to` x) <*> ((t `to` f) <*> (do f' <- force (Var f); apply f' (Var @a x)))

cbvVar :: (KnownLType a) => VarId a -> Term' (CBVType a)
cbvVar = Return . Var

type CBVType a = Up a

type CBVLolly a b = Down (a `Lolly` CBVType b)

exampleTerm ::
  forall a0 a1 b.
  (KnownLType (a0 :: LType Positive)) =>
  (KnownLType (a1 :: LType Positive)) =>
  (KnownLType b) =>
  M (Term' (CBVType b))
exampleTerm = do
  x <- fresh "x"
  y <- fresh "y"
  let one = "one"
  let two = "two"
  let minus = "sub"

  inner <-
    cbvApply <$> cbvApply (cbvVar minus) (cbvVar @a0 x) <*> pure (cbvVar @a1 y)

  lam_ <- cbvLam @a0 x =<< (cbvLam @a1 y =<< inner)

  applied <- cbvApply <$> cbvApply lam_ (cbvVar @a0 one) <*> pure (cbvVar @a1 two)
  applied

data TypedTerm p where
  TypedTerm ::
    forall (p :: Polarity) (t :: LType p).
    Term p t ->
    TypedTerm p

deriving instance Show (TypedTerm p)

showTypedTerm :: TypedTerm p -> String
showTypedTerm (TypedTerm t) = showTerm t

termType :: Term p t -> SLType p t
termType = \case
  Var {} -> know
  Mu {} -> error "Mu"
  Pair {} -> know
  MuPair {} -> know
  Unit {} -> error "Unit"
  MuUnit {} -> error "MuUnit"
  OneDot {} -> error "OneDot"
  TwoDot {} -> error "TwoDot"
  MuDot {} -> error "MuDot"
  EmptyCase {} -> error "EmptCase"
  Return {} -> know
  MuReturn {} -> know
  Debug {} -> know
  Stop {} -> know
  Sub {} -> error "Sub"
  IntLit {} -> know

type Subst = Map.Map String (TypedTerm Positive)

modi :: (Monad m) => Term Positive t -> VarId t -> State.StateT Subst m ()
modi t x =
  State.modify'
    ( case t of
        Var v -> \m -> case Map.lookup v m of
          Nothing -> Map.insert x (TypedTerm t) m
          Just tt -> Map.delete v (Map.insert x tt m)
        -- Do pairs too
        _ -> Map.insert x (TypedTerm t)
    )

lookupLinear ::
  (Monad m) =>
  String ->
  Term Positive t ->
  State.StateT Subst m (Term Positive t)
lookupLinear x v =
  State.gets (Map.lookup x) >>= \case
    Just (TypedTerm t2) -> do
      State.modify' (Map.delete x)
      case eqSLType (termType t2) (termType v) of
        Just Dict -> pure t2
        Nothing ->
          error
            ( unlines
                [ "Mismatched types",
                  showTerm v ++ " :: " ++ show (termType v),
                  "env("
                    ++ showTerm v
                    ++ ") = "
                    ++ showTerm t2
                    ++ " :: "
                    ++ show (termType t2)
                ]
            )
    Nothing ->
      error
        ( unlines
            [ "Missing key " ++ x,
              show (termType v)
            ]
        )

-- p21
-- These are the opposite way round!
step :: (Monad m) => Computation -> State.StateT Subst m (Maybe Computation)
step (Computation (Mu x c) t) = do
  modi t x
  pure (Just c)
step (Computation (Return t) (MuReturn x c)) = do
  modi t x
  pure (Just c)
-- Would be nice to explicity convert heap values to stack values
step (Computation t1 v@(Var x)) = do
  t2 <- lookupLinear x v
  pure (Just (Computation t1 t2))
step (Computation (MuPair (x, y) c) (Pair (t, u))) = do
  modi t x
  modi u y
  pure (Just c)
step (Computation (Sub c) (Pair (v@(Var t), t2))) = do
  t1 <- lookupLinear t v
  pure (Just (Computation (Sub c) (Pair (t1, t2))))
step (Computation (Sub c) (Pair (t1, v@(Var t)))) = do
  t2 <- lookupLinear t v
  pure (Just (Computation (Sub c) (Pair (t1, t2))))
step (Computation (Sub c) (Pair (IntLit i1, IntLit i2))) = do
  pure (Just (Computation c (IntLit (i1 - i2))))
step (Computation (Stop {}) _) = pure Nothing
step (Computation t1 t2) = error (show (termType t1) ++ " | " ++ show (termType t2))

type TermType = CBVType LInt

macro ::
  forall (t :: LType Positive) (t' :: LType Positive) c.
  (KnownLType t) =>
  (KnownLType c) =>
  (KnownLType t') =>
  ((VarId t', VarId t) -> M (Term Negative (Perp c), Term Positive c)) ->
  M (Term Positive (Perp (Up ('Tensor t t'))))
macro x = do
  stack <- fresh "stack"
  arg <- fresh "arg"
  rest <- fresh "rest"
  ii <- x (arg, rest)
  pure $
    MuReturn @(Tensor t t')
      stack
      ( Computation
          ( MuPair @t @t'
              (arg, rest)
              (uncurry Computation ii)
          )
          (Var @(Tensor t t') stack)
      )

example :: IO ()
example = do
  let term :: Term' TermType
      term = runM (exampleTerm @LInt @LInt @LInt)

  let loop c =
        step c >>= \case
          Nothing -> pure ()
          Just c' -> do
            lift (putStrLn "--")
            m <- State.get
            flip mapM_ (Map.toList m) $ \(k, v) -> do
              lift (putStrLn (k ++ ": " ++ showTypedTerm v))
            lift (putStrLn (showComputation c'))
            loop c'

  let c =
        Computation @(Perp TermType)
          term
          ( MuReturn @LInt
              "theres"
              (Computation Stop (Var @LInt "theres"))
          )

  putStrLn (showComputation c)

  let outer = runM $ do
        macro
          @LInt
          @(Down (Up (Tensor LInt RestOfStack)))
          $ \(arg1, rest) -> do
            ii <- macro @LInt @RestOfStack $ \(arg2, bottom) ->
              pure
                ( Sub
                    ( Mu
                        @LInt
                        "res"
                        ( Computation
                            @(Tensor LInt RestOfStack)
                            ( MuPair
                                @LInt
                                @RestOfStack
                                ("theup", "thestop")
                                ( Computation
                                    @(Perp (Up LInt))
                                    (Return (Var "theup"))
                                    (Var "thestop")
                                )
                            )
                            (Pair (Var "res", Var bottom))
                        )
                    ),
                  Pair (Var arg1, Var arg2)
                )

            pure (Return ii, Var rest)

  flip
    State.evalStateT
    ( Map.fromList
        [ ("one", TypedTerm (IntLit 1)),
          ("two", TypedTerm (IntLit 2)),
          ("sub", TypedTerm outer)
        ]
    )
    (loop c)

type RestOfStack = Down (Perp LInt)
