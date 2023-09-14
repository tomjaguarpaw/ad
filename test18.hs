{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

module Main where

import Data.Functor.Const (Const (Const))
import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy (Proxy))
import Prelude hiding (pi)

-- User code
data Sum
  = A Int
  | B Bool
  | C Char

data Product = Product Int Bool Char

newtype SumFamily' t = SumFamily' {getSumFamily :: SumFamily t}

showSum :: Sum -> String
showSum = genericShowSum sumConNames sumToGeneric

example :: IO ()
example = mapM_ (putStrLn . showSum) [A 1, B True, C 'x']

-- Generics library
data Sigma s f where
  Sigma :: s i -> f i -> Sigma s f

class Tag (st :: t -> Type) where
  data Pi st :: (t -> Type) -> Type
  type Tags st :: [t]

  getPi :: forall (i :: t) (f :: t -> *). Pi st f -> st i -> f i
  makePi :: (forall (i :: t). st i -> f i) -> Pi st f

class FieldTypes (st :: t -> Type) where
  type FieldType st (i :: t) :: Type
  type FieldType' st :: t -> Type
  type ForallCTag st (c :: Type -> Constraint) :: Constraint

  getFieldType :: FieldType' st i -> FieldType st i

  forallCTag'' ::
    (ForallCTag st c) =>
    Proxy c ->
    st i ->
    ((c (FieldType st i)) => r) ->
    r

forallCTag ::
  forall c st r i.
  (FieldTypes st) =>
  (ForallCTag st c) =>
  st i ->
  ((c (FieldType st i)) => r) ->
  r
forallCTag = forallCTag'' (Proxy @c)

mashPiSigma ::
  (Tag st) =>
  Pi st f1 ->
  Sigma st f2 ->
  (forall i. st i -> f1 i -> f2 i -> r) ->
  r
mashPiSigma pi (Sigma s f) k = k s (getPi pi s) f

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

genericShowSum ::
  forall st x.
  (Tag st) =>
  (FieldTypes st) =>
  (ForallCTag st Show) =>
  Pi st (Const String) ->
  (x -> Sigma st (FieldType' st)) ->
  x ->
  String
genericShowSum pi f =
  genericShowSum' pi f (\t -> forallCTag @Show t show . getFieldType @_ @st)

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

instance FieldTypes SSumTag where
  type FieldType SSumTag t = SumFamily t
  type FieldType' SSumTag = SumFamily'

  getFieldType = getSumFamily

  -- Requires UndecidableInstances. Could probably hack around this.
  type ForallCTag SSumTag c = ForallCSumTag' c (Tags SSumTag)

  forallCTag'' = \(Proxy :: Proxy c) -> forallCSumTag @c

type family SumFamily (t :: SumTag) :: Type where
  SumFamily ATag = Int
  SumFamily BTag = Bool
  SumFamily CTag = Char

type family ForallCSumTag' c (ts :: [SumTag]) :: Constraint where
  ForallCSumTag' _ '[] = ()
  ForallCSumTag' c (t : ts) = (c (SumFamily t), ForallCSumTag' c ts)

type ForallCSumTag (c :: Type -> Constraint) = ForallCSumTag' c (Tags SSumTag)

forallCSumTag ::
  forall c i r.
  (ForallCSumTag c) =>
  SSumTag i ->
  ((c (SumFamily i)) => r) ->
  r
forallCSumTag = \case
  SATag -> id
  SBTag -> id
  SCTag -> id

sumConNames :: Pi SSumTag (Const String)
sumConNames =
  makePi $
    Const . \case
      SATag -> "A"
      SBTag -> "B"
      SCTag -> "C"

sumToGeneric :: Sum -> Sigma SSumTag SumFamily'
sumToGeneric = \case
  A p -> Sigma SATag (SumFamily' p)
  B p -> Sigma SBTag (SumFamily' p)
  C p -> Sigma SCTag (SumFamily' p)

genericToSum :: Sigma SSumTag SumFamily' -> Sum
genericToSum = \case
  Sigma t (SumFamily' p) -> case t of
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

type family ProductFamily (t :: ProductTag) :: Type where
  ProductFamily Field1 = Int
  ProductFamily Field2 = Bool
  ProductFamily Field3 = Char

newtype ProductFamily' t = ProductFamily' {getProductFamily :: ProductFamily t}

productToGeneric :: Product -> Pi SProductTag ProductFamily'
productToGeneric (Product f1 f2 f3) =
  makePi $
    ( ProductFamily' . \case
        SField1 -> f1
        SField2 -> f2
        SField3 -> f3
    )

genericToProduct :: Pi SProductTag ProductFamily' -> Product
genericToProduct pi =
  Product (getField SField1) (getField SField2) (getField SField3)
  where
    getField :: forall i. SProductTag i -> ProductFamily i
    getField = getProductFamily . getPi pi
