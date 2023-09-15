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

-- Section: User code

data Sum a b
  = A Int
  | B Bool
  | C a
  | D a
  | E b

data Product a = Product Int Bool a

showSum :: forall a b. (Show a, Show b) => Sum a b -> String
showSum = genericShowSum

showProduct :: forall a. (Show a) => Product a -> String
showProduct = genericShowProduct

main :: IO ()
main = do
  mapM_ (putStrLn . showSum) [A 1, B True, C 'x', D 'y', E ()]
  putStrLn (showProduct (Product 1 True 'x'))

-- Generics library
data Sigma s f where
  Sigma :: s i -> f i -> Sigma s f

class Tag (st :: t -> Type) where
  data Pi st :: (t -> Type) -> Type
  type Tags st :: [t]

  getPi :: forall (i :: t) (f :: t -> Type). Pi st f -> st i -> f i
  makePi :: (forall (i :: t). st i -> f i) -> Pi st f

  traversePi ::
    forall (f :: t -> Type) (g :: t -> Type) m.
    (Applicative m) =>
    (forall (i :: t). st i -> f i -> m (g i)) ->
    Pi st f ->
    m (Pi st g)

  provideConstraint' ::
    (ForeachField (f :: FunctionSymbol st) c) =>
    Proxy c ->
    Proxy f ->
    st i ->
    ((c (FieldType f i)) => r) ->
    r

type FunctionSymbol' t (st :: t -> Type) = Proxy st -> Type

type FunctionSymbol (st :: t -> Type) = FunctionSymbol' t st

type family St (a :: FunctionSymbol st) where
  St (f :: FunctionSymbol st) = st

class FieldTypes (f :: FunctionSymbol' t st) where
  type FieldType' t st f (i :: t) :: Type

-- Just to implicitly pass t and st
type FieldType (f :: FunctionSymbol' t st) i = FieldType' t st f i

type family
  ForeachField' t st (f :: FunctionSymbol' t st) c (ts :: [t]) ::
    Constraint
  where
  ForeachField' _ _ _ _ '[] = ()
  ForeachField' t st f c (i : is) =
    (c (FieldType' t st f i), ForeachField' t st f c is)

type ForeachField (f :: FunctionSymbol' t st) c =
  ForeachField' t st f c (Tags st)

provideConstraint ::
  forall c f r i st.
  (st ~ St f) =>
  (Tag st) =>
  (ForeachField f c) =>
  st i ->
  ((c (FieldType f i)) => r) ->
  r
provideConstraint = provideConstraint' (Proxy @c) (Proxy @f)

newtype Newtyped f i = Newtyped {getNewtyped :: FieldType f i}

mashPiSigma ::
  (Tag st) =>
  Pi st f1 ->
  Sigma st f2 ->
  (forall i. st i -> f1 i -> f2 i -> r) ->
  r
mashPiSigma pi (Sigma s f) k = k s (getPi pi s) f

traversePi_ ::
  (Applicative m, Tag st) =>
  (forall (i :: t). st i -> f i -> m ()) ->
  Pi st f ->
  m ()
-- This implementation could be better
traversePi_ f = fmap (const ()) . traversePi (\st -> fmap Const . f st)

toListPi :: (Tag st) => (forall (i :: t). st i -> f i -> a) -> Pi st f -> [a]
toListPi f = getConst . traversePi_ (\st x -> Const [f st x])

showField ::
  forall st (f :: FunctionSymbol st) i.
  (Tag st) =>
  (ForeachField f Show) =>
  st i ->
  Newtyped f i ->
  String
showField t = provideConstraint @Show @f t show . getNewtyped

genericShowSum' ::
  forall st x (f :: FunctionSymbol st).
  (Tag st) =>
  (ForeachField f Show) =>
  Pi st (Const String) ->
  (x -> Sigma st (Newtyped f)) ->
  x ->
  String
genericShowSum' pi f x = mashPiSigma pi (f x) $ \t (Const conName) field ->
  conName ++ " " ++ showField t field

genericShowSum ::
  forall sum st (f :: FunctionSymbol st).
  (Tag st) =>
  (IsSum sum f) =>
  (ForeachField f Show) =>
  sum ->
  String
genericShowSum =
  genericShowSum' @_ @sum (sumConNames @_ @sum) (sumToGeneric @_ @sum)

genericShowProduct' ::
  forall st x (f :: FunctionSymbol st).
  (ForeachField f Show) =>
  (Tag st) =>
  String ->
  (x -> Pi st (Newtyped f)) ->
  x ->
  String
genericShowProduct' conName f x =
  conName ++ " " ++ unwords (toListPi showField (f x))

genericShowProduct ::
  forall product st (f :: FunctionSymbol st).
  (Tag st, IsProduct product f, ForeachField f Show) =>
  product ->
  String
genericShowProduct =
  genericShowProduct' @st (productConName @_ @product) productToGeneric

class IsSum (sum :: Type) (sumf :: FunctionSymbol st) | sum -> sumf, sumf -> sum where
  sumConNames :: Pi st (Const String)
  sumToGeneric :: sum -> Sigma st (Newtyped sumf)
  genericToSum :: Sigma st (Newtyped sumf) -> sum

class
  IsProduct (product :: Type) (productf :: FunctionSymbol st)
    | product -> productf,
      productf -> product
  where
  productConName :: String
  productToGeneric :: product -> Pi st (Newtyped productf)
  genericToProduct :: Pi st (Newtyped productf) -> product

-- Generated code

-- For data Sum
data SumTag = ATag | BTag | CTag | DTag | ETag

data SSumTag t where
  SATag :: SSumTag ATag
  SBTag :: SSumTag BTag
  SCTag :: SSumTag CTag
  SDTag :: SSumTag DTag
  SETag :: SSumTag ETag

instance Tag SSumTag where
  data Pi SSumTag f = PiSSumTag (f ATag) (f BTag) (f CTag) (f DTag) (f ETag)
  type Tags SSumTag = [ATag, BTag, CTag, DTag, ETag]
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

data SumF (a :: Type) (b :: Type) (t :: Proxy SSumTag)

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

  sumToGeneric = \case
    A p -> Sigma SATag (Newtyped p)
    B p -> Sigma SBTag (Newtyped p)
    C p -> Sigma SCTag (Newtyped p)
    D p -> Sigma SDTag (Newtyped p)
    E p -> Sigma SETag (Newtyped p)

  genericToSum = \case
    Sigma t (getNewtyped -> p) -> case t of
      SATag -> A p
      SBTag -> B p
      SCTag -> C p
      SDTag -> D p
      SETag -> E p

-- For data Product
data ProductTag = Field1 | Field2 | Field3

data SProductTag t where
  SField1 :: SProductTag Field1
  SField2 :: SProductTag Field2
  SField3 :: SProductTag Field3

instance Tag SProductTag where
  data Pi SProductTag f = PiSProductTag (f Field1) (f Field2) (f Field3)
  type Tags SProductTag = [Field1, Field2, Field3]

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

data ProductF (a :: Type) (t :: Proxy SProductTag)

instance FieldTypes (ProductF a) where
  type FieldType' _ _ (ProductF a) t = ProductFamily a t

type family ProductFamily (a :: Type) (t :: ProductTag) :: Type where
  ProductFamily _ Field1 = Int
  ProductFamily _ Field2 = Bool
  ProductFamily a Field3 = a

instance IsProduct (Product a) (ProductF a) where
  productConName = "Product"
  productToGeneric (Product f1 f2 f3) =
    makePi
      ( Newtyped . \case
          SField1 -> f1
          SField2 -> f2
          SField3 -> f3
      )

  genericToProduct pi =
    Product (getField SField1) (getField SField2) (getField SField3)
    where
      getField :: forall i. SProductTag i -> ProductFamily a i
      getField = getNewtyped . getPi pi
