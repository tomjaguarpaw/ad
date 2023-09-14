{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
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
import Data.List (intercalate)
import Data.Proxy (Proxy (Proxy))
import Prelude hiding (pi)

-- User code
data Sum
  = A Int
  | B Bool
  | C Char

data Product = Product Int Bool Char

showSum :: Sum -> String
showSum = genericShowSum sumConNames sumToGeneric

showProduct :: Product -> String
showProduct = genericShowProduct productConName productToGeneric

main :: IO ()
main = do
  mapM_ (putStrLn . showSum) [A 1, B True, C 'x']
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
    ((c (FieldType' f i)) => r) ->
    r

type FunctionSymbol (st :: t -> Type) = Proxy st -> Type

type family F (a :: FunctionSymbol st) where
  F (f :: FunctionSymbol st) = st

type family G (a :: FunctionSymbol st) where
  G (f :: FunctionSymbol (st :: t -> Type)) = t

class FieldTypes (f :: FunctionSymbol (st :: t -> Type)) where
  type FieldType t st f (i :: t) :: Type

type FieldType' f i = FieldType (G f) (F f) f i

type family ForeachField' (f :: FunctionSymbol st) c (ts :: [t]) :: Constraint where
  ForeachField' _ _ '[] = ()
  ForeachField' f c (i : is) =
    (c (FieldType' f i), ForeachField' f c is)

type ForeachField (f :: FunctionSymbol st) c = ForeachField' f c (Tags st)

provideConstraint ::
  forall c st (f :: FunctionSymbol st) r i.
  (Tag st) =>
  (FieldTypes f) =>
  (ForeachField f c) =>
  st i ->
  ((c (FieldType' f i)) => r) ->
  r
provideConstraint = provideConstraint' (Proxy @c) (Proxy @f)

newtype Family' f t = Family' {getFamily :: FieldType (G f) (F f) f t}

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

-- `family` is a keyword?!
genericShowSum' ::
  (Tag st) =>
  Pi st (Const String) ->
  (x -> Sigma st family') ->
  (forall i. st i -> family' i -> String) ->
  x ->
  String
genericShowSum' pi f g x = mashPiSigma pi (f x) $ \t (Const conName) field ->
  conName ++ " " ++ g t field

genericShow ::
  forall st (f :: FunctionSymbol st) i.
  (FieldTypes f) =>
  (Tag st) =>
  (ForeachField f Show) =>
  st i ->
  Family' f i ->
  String
genericShow t = provideConstraint @Show @_ @f t show . getFieldType @f

genericShowSum ::
  forall st x (f :: FunctionSymbol st).
  (Tag st) =>
  (FieldTypes f) =>
  (ForeachField f Show) =>
  Pi st (Const String) ->
  (x -> Sigma st (Family' f)) ->
  x ->
  String
genericShowSum pi f = genericShowSum' pi f (genericShow @_ @f)

genericShowProduct ::
  forall st x (f :: FunctionSymbol st).
  (FieldTypes f) =>
  (ForeachField f Show) =>
  (Tag st) =>
  String ->
  (x -> Pi st (Family' f)) ->
  x ->
  String
genericShowProduct conName f x =
  conName ++ " " ++ intercalate " " (toListPi genericShow (f x))

getFieldType ::
  forall f i.
  (FieldTypes f) =>
  Family' f i ->
  FieldType' f i
getFieldType = getFamily

-- Generated code

-- For data Sum
data SumTag = ATag | BTag | CTag

data SSumTag t where
  SATag :: SSumTag ATag
  SBTag :: SSumTag BTag
  SCTag :: SSumTag CTag

instance Tag SSumTag where
  data Pi SSumTag f = PiSSumTag (f ATag) (f BTag) (f CTag)
  type Tags SSumTag = [ATag, BTag, CTag]
  getPi (PiSSumTag f1 f2 f3) = \case
    SATag -> f1
    SBTag -> f2
    SCTag -> f3
  makePi f = PiSSumTag (f SATag) (f SBTag) (f SCTag)

  traversePi f (PiSSumTag a b c) =
    PiSSumTag <$> f SATag a <*> f SBTag b <*> f SCTag c

  provideConstraint' = \_ _ -> \case
    SATag -> id
    SBTag -> id
    SCTag -> id

data SumF (a :: Proxy SSumTag)

instance FieldTypes SumF where
  type FieldType _ _ SumF t = SumFamily t

type family SumFamily (t :: SumTag) :: Type where
  SumFamily ATag = Int
  SumFamily BTag = Bool
  SumFamily CTag = Char

sumConNames :: Pi SSumTag (Const String)
sumConNames =
  makePi $
    Const . \case
      SATag -> "A"
      SBTag -> "B"
      SCTag -> "C"

sumToGeneric :: Sum -> Sigma SSumTag (Family' SumF)
sumToGeneric = \case
  A p -> Sigma SATag (Family' p)
  B p -> Sigma SBTag (Family' p)
  C p -> Sigma SCTag (Family' p)

genericToSum :: Sigma SSumTag (Family' SumF) -> Sum
genericToSum = \case
  Sigma t (getFieldType @SumF -> p) -> case t of
    SATag -> A p
    SBTag -> B p
    SCTag -> C p

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

data ProductF (a :: Proxy SProductTag)

instance FieldTypes ProductF where
  type FieldType _ _ ProductF t = ProductFamily t

type family ProductFamily (t :: ProductTag) :: Type where
  ProductFamily Field1 = Int
  ProductFamily Field2 = Bool
  ProductFamily Field3 = Char

productToGeneric :: Product -> Pi SProductTag (Family' ProductF)
productToGeneric (Product f1 f2 f3) =
  makePi $
    ( Family' . \case
        SField1 -> f1
        SField2 -> f2
        SField3 -> f3
    )

genericToProduct :: Pi SProductTag (Family' ProductF) -> Product
genericToProduct pi =
  Product (getField SField1) (getField SField2) (getField SField3)
  where
    getField :: forall i. SProductTag i -> ProductFamily i
    getField = getFamily . getPi pi

productConName :: String
productConName = "Product"
