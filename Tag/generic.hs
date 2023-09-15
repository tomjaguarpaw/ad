{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

module Main where

import Data.Functor.Const (Const (Const, getConst))
import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy (Proxy))
import Prelude hiding (pi)

{- Section: Summary of the idea

The idea of this library is to take a sum type like

    data Sum arg1 ... argn = C1 t1 | ... | Cm tm

and generate a Sigma type that is isomorphic to it

    data SumTag = C1 | ... | Cm

    f = \case { C1 -> t1, ..., Cm -> tm }

    Sigma (c :: SumTag). f c

and to take a product type like

    data Sum arg1 ... argn = C t1 tm

and generate a Pi type that is isomorphic to it

    data ProductTag = F1 | ... | Fm

    f = \case { F1 -> t1, ..., Fm -> tm }

    Pi (t :: ProductTag). f t

(The isomorphisms are expressed in this library though sumToSigma,
sigmaToSum, productToPi and piToProduct.)

The hope is that it's easier to work generically with Sigma and Pi
types than arbitrary Haskell data definitions.  Of course, to code up
Sigma and Pi types in Haskell requires a fair bit of machinery, and
that's the bulk of this library!

-}

-- Section: User code

-- Currently this library works for types with multiple constructors
-- each with a single field ...
data Sum a b
  = A Int
  | B Bool
  | C a
  | D a
  | E b

-- ... or with a single constructor with multiple fields.
data Product a = Product Int Bool a

-- We can obtain show generically!
showSum :: (Show a, Show b) => Sum a b -> String
showSum = genericShowSum

-- We can obtain show generically!
showProduct :: (Show a) => Product a -> String
showProduct = genericShowProduct

main :: IO ()
main = do
  mapM_ (putStrLn . showSum) [A 1, B True, C 'x', D 'y', E ()]
  putStrLn (showProduct (Product 1 True 'x'))

-- Section: Generics library
data Sigma t (st :: t -> Type) f where
  Sigma :: st i -> f i -> Sigma t st f

-- | @st@ is the "singleton type" version of @t@
class Tag t (st :: t -> Type) where
  type Singleton t :: t -> Type

  -- | All the types of kind @t@
  type Tags t st :: [t]

  data Pi t st :: (t -> Type) -> Type

  getPi :: forall (i :: t) (f :: t -> Type). Pi t st f -> st i -> f i
  makePi :: (forall (i :: t). st i -> f i) -> Pi t st f

  traversePi ::
    forall (f :: t -> Type) (g :: t -> Type) m.
    (Applicative m) =>
    (forall (i :: t). st i -> f i -> m (g i)) ->
    Pi t st f ->
    m (Pi t st g)

  provideConstraint' ::
    (ForeachField (f :: FunctionSymbol st) c) =>
    Proxy c ->
    Proxy f ->
    st i ->
    ((c (FieldType f i)) => r) ->
    r

-- Useful for obtaining @st@ and @t@ without making them visible in
-- signatures.
type FunctionSymbol' t (st :: t -> Type) = Proxy st -> Type

-- Useful for obtaining @st@ and @t@ without making them visible in
-- signatures.
type FunctionSymbol (st :: t -> Type) = FunctionSymbol' t st

-- This is a defunctionalized mapping from @t@ to @Type@, represented
-- by the function symbol @f@.  We need this defunctionalized version
-- because we can't partially apply type synonyms.
class FieldTypes (f :: FunctionSymbol' t st) where
  type FieldType' t st f (i :: t) :: Type

-- Useful for passing @t@ and @st@ implicitly, without bringing them
-- into scope.
type FieldType (f :: FunctionSymbol' t st) i = FieldType' t st f i

-- | @ForEachField f c@ means that for each @i@ of kind @t@,
-- @FieldType f i@ has an instance for @c@.
type ForeachField (f :: FunctionSymbol' t st) c =
  ForeachField' t st f c (Tags t st)

-- | The implementation of @ForeachField@
type family
  ForeachField' t st (f :: FunctionSymbol st) c (ts :: [t]) ::
    Constraint
  where
  ForeachField' _ _ _ _ '[] = ()
  ForeachField' t st f c (i : is) =
    (c (FieldType' t st f i), ForeachField' t st f c is)

-- | Witness to the property of @ForEachField@
provideConstraint ::
  forall c t st (f :: FunctionSymbol st) r i.
  (Tag t st) =>
  (ForeachField f c) =>
  st i ->
  ((c (FieldType f i)) => r) ->
  r
provideConstraint = provideConstraint' (Proxy @c) (Proxy @f)

-- | We can't partially apply type families so instead we
-- defunctionalize them to a symbol @f@ and then wrap them up in a
-- newtype for use when we do need to partially apply them.
newtype Newtyped f i = Newtyped {getNewtyped :: FieldType f i}

mashPiSigma ::
  (Tag t st) =>
  Pi t st f1 ->
  Sigma t st f2 ->
  (forall i. st i -> f1 i -> f2 i -> r) ->
  r
mashPiSigma pi (Sigma s f) k = k s (getPi pi s) f

traversePi_ ::
  (Applicative m, Tag t st) =>
  (forall (i :: t). st i -> f i -> m ()) ->
  Pi t st f ->
  m ()
-- This implementation could be better
traversePi_ f = fmap (const ()) . traversePi (\st -> fmap Const . f st)

toListPi :: (Tag t st) => (forall (i :: t). st i -> f i -> a) -> Pi t st f -> [a]
toListPi f = getConst . traversePi_ (\st x -> Const [f st x])

-- Sum types will (or could -- that isn't implemented yet) have an
-- instance of this class generated for them
class
  IsSum (sum :: Type) (sumf :: FunctionSymbol' t st)
    | sum -> sumf,
      sumf -> sum
  where
  sumConNames :: Pi t st (Const String)
  sumToSigma :: sum -> Sigma t st (Newtyped sumf)
  sigmaToSum :: Sigma t st (Newtyped sumf) -> sum

-- Product types will (or could -- that isn't implemented yet) have an
-- instance of this class generated for them
class
  IsProduct (product :: Type) (productf :: FunctionSymbol' t st)
    | product -> productf,
      productf -> product
  where
  productConName :: String
  productToPi :: product -> Pi t st (Newtyped productf)
  piToProduct :: Pi t st (Newtyped productf) -> product

-- Section: Client of the generics library, between the generics
-- library and the user.  It provides a generic implementation of
-- Show.

showField ::
  forall t st (f :: FunctionSymbol st) i.
  (Tag t st, ForeachField f Show) =>
  st i ->
  Newtyped f i ->
  String
showField t = provideConstraint @Show @_ @_ @f t show . getNewtyped

genericShowSum' ::
  forall t st x (f :: FunctionSymbol st).
  (Tag t st, ForeachField f Show) =>
  Pi t st (Const String) ->
  (x -> Sigma t st (Newtyped f)) ->
  x ->
  String
genericShowSum' pi f x = mashPiSigma pi (f x) $ \t (Const conName) field ->
  conName ++ " " ++ showField t field

genericShowSum ::
  forall sum t st (f :: FunctionSymbol st).
  (Tag t st, IsSum sum f, ForeachField f Show) =>
  sum ->
  String
genericShowSum =
  genericShowSum' @_ @_ @sum (sumConNames @_ @_ @sum) sumToSigma

genericShowProduct' ::
  forall t st x (f :: FunctionSymbol st).
  (ForeachField f Show, Tag t st) =>
  String ->
  (x -> Pi t st (Newtyped f)) ->
  x ->
  String
genericShowProduct' conName f x =
  conName ++ " " ++ unwords (toListPi showField (f x))

genericShowProduct ::
  forall product t st (f :: FunctionSymbol st).
  (Tag t st, IsProduct product f, ForeachField f Show) =>
  product ->
  String
genericShowProduct =
  genericShowProduct' @t @st (productConName @_ @_ @product) productToPi

-- Section: Generated code.  The generics library could in principle
-- generate this, but that isn't implemented yet.

-- For data Sum

-- | One value for each constructor of the sum type
data SumTag = ATag | BTag | CTag | DTag | ETag

-- | The singleton version of the above
data SSumTag t where
  SATag :: SSumTag ATag
  SBTag :: SSumTag BTag
  SCTag :: SSumTag CTag
  SDTag :: SSumTag DTag
  SETag :: SSumTag ETag

instance Tag SumTag SSumTag where
  type Singleton SumTag = SSumTag
  data Pi SumTag SSumTag f = PiSSumTag (f ATag) (f BTag) (f CTag) (f DTag) (f ETag)
  type Tags SumTag SSumTag = [ATag, BTag, CTag, DTag, ETag]
  getPi (PiSSumTag f1 f2 f3 f4 f5) = \case
    SATag -> f1
    SBTag -> f2
    SCTag -> f3
    SDTag -> f4
    SETag -> f5
  makePi f = PiSSumTag (f SATag) (f SBTag) (f SCTag) (f SDTag) (f SETag)

  traversePi f (PiSSumTag a b c d e) =
    PiSSumTag <$> f SATag a <*> f SBTag b <*> f SCTag c <*> f SDTag d <*> f SETag e

  provideConstraint' = \_ _ -> \case
    SATag -> id
    SBTag -> id
    SCTag -> id
    SDTag -> id
    SETag -> id

-- | A symbol used so that we can defunctionalize the mapping
-- @SumFamily@
data SumF (a :: Type) (b :: Type) (t :: Proxy (Singleton SumTag))

instance FieldTypes (SumF a b) where
  type FieldType' _ _ (SumF a b) t = SumFamily a b t

type family SumFamily (a :: Type) (b :: Type) (t :: SumTag) :: Type where
  SumFamily _ _ ATag = Int
  SumFamily _ _ BTag = Bool
  SumFamily a _ CTag = a
  SumFamily a _ DTag = a
  SumFamily _ b ETag = b

instance IsSum (Sum a b) (SumF a b) where
  sumConNames =
    makePi $
      Const . \case
        SATag -> "A"
        SBTag -> "B"
        SCTag -> "C"
        SDTag -> "D"
        SETag -> "E"

  sumToSigma = \case
    A p -> Sigma SATag (Newtyped p)
    B p -> Sigma SBTag (Newtyped p)
    C p -> Sigma SCTag (Newtyped p)
    D p -> Sigma SDTag (Newtyped p)
    E p -> Sigma SETag (Newtyped p)

  sigmaToSum = \case
    Sigma t (getNewtyped -> p) -> case t of
      SATag -> A p
      SBTag -> B p
      SCTag -> C p
      SDTag -> D p
      SETag -> E p

-- For data Product

-- One value for each constructor of the product type
data ProductTag = Field1 | Field2 | Field3

-- The singleton version of the above
data SProductTag t where
  SField1 :: SProductTag Field1
  SField2 :: SProductTag Field2
  SField3 :: SProductTag Field3

instance Tag ProductTag SProductTag where
  type Singleton ProductTag = SProductTag
  data Pi ProductTag SProductTag f = PiSProductTag (f Field1) (f Field2) (f Field3)
  type Tags ProductTag SProductTag = [Field1, Field2, Field3]

  getPi (PiSProductTag f1 f2 f3) = \case
    SField1 -> f1
    SField2 -> f2
    SField3 -> f3
  makePi f = PiSProductTag (f SField1) (f SField2) (f SField3)

  traversePi f (PiSProductTag f1 f2 f3) =
    PiSProductTag <$> f SField1 f1 <*> f SField2 f2 <*> f SField3 f3

  provideConstraint' = \_ _ -> \case
    SField1 -> id
    SField2 -> id
    SField3 -> id

-- | A symbol used so that we can defunctionalize the mapping
-- @ProductFamily@
data ProductF (a :: Type) (t :: Proxy (Singleton ProductTag))

instance FieldTypes (ProductF a) where
  type FieldType' _ _ (ProductF a) t = ProductFamily a t

type family ProductFamily (a :: Type) (t :: ProductTag) :: Type where
  ProductFamily _ Field1 = Int
  ProductFamily _ Field2 = Bool
  ProductFamily a Field3 = a

instance IsProduct (Product a) (ProductF a) where
  productConName = "Product"
  productToPi (Product f1 f2 f3) =
    makePi
      ( Newtyped . \case
          SField1 -> f1
          SField2 -> f2
          SField3 -> f3
      )

  piToProduct pi =
    Product (getField SField1) (getField SField2) (getField SField3)
    where
      getField :: forall i. Singleton ProductTag i -> ProductFamily a i
      getField = getNewtyped . getPi pi
