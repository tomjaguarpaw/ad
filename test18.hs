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
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

module Main where

import Data.Functor.Const (Const (Const))
import Data.Kind (Constraint, Type)
import Prelude hiding (pi)

data Sum
  = A Int
  | B Bool
  | C Char

data Product = Product Int Bool Char

data SumTag = ATag | BTag | CTag

data SSumTag t where
  SATag :: SSumTag ATag
  SBTag :: SSumTag BTag
  SCTag :: SSumTag CTag

data ProductTag = Field1 | Field2 | Field3

data SProductTag t where
  SField1 :: SProductTag Field1
  SField2 :: SProductTag Field2
  SField3 :: SProductTag Field3

data Sigma s f where
  Sigma :: s i -> f i -> Sigma s f

class Tag (st :: t -> Type) where
  data Pi st :: (t -> Type) -> Type
  type ForallC st (c :: z -> Constraint) (f :: t -> z) :: Constraint

  getPi :: forall (i :: t) (f :: t -> *). Pi st f -> st i -> f i
  makePi :: (forall (i :: t). st i -> f i) -> Pi st f

mashPiSigma ::
  (Tag st) =>
  Pi st f1 ->
  Sigma st f2 ->
  (forall i. st i -> f1 i -> f2 i -> r) ->
  r
mashPiSigma pi (Sigma s f) k =
  k s (getPi pi s) f

instance Tag SProductTag where
  data Pi SProductTag f = PiSProductTag (f Field1) (f Field2) (f Field3)
  type ForallC SProductTag c f = (c (f Field1), c (f Field2), c (f Field3))

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

instance Tag SSumTag where
  data Pi SSumTag f = PiSSumTag (f ATag) (f BTag) (f CTag)
  type ForallC SSumTag c f = (c (f ATag), c (f BTag), c (f CTag))
  getPi (PiSSumTag f1 f2 f3) = \case
    SATag -> f1
    SBTag -> f2
    SCTag -> f3
  makePi f = PiSSumTag (f SATag) (f SBTag) (f SCTag)

type family SumFamily (t :: SumTag) :: Type where
  SumFamily ATag = Int
  SumFamily BTag = Bool
  SumFamily CTag = Char

type ForallCSumTag (c :: Type -> Constraint) =
  ( c (SumFamily ATag),
    c (SumFamily BTag),
    c (SumFamily CTag)
  )

forallCSumTag ::
  (ForallCSumTag c) =>
  SSumTag i ->
  ((c (SumFamily i)) => r) ->
  r
forallCSumTag = \case
  SATag -> id
  SBTag -> id
  SCTag -> id

newtype SumFamily' t = SumFamily' {getSumFamily :: SumFamily t}

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

-- `family` is a keyword?!
genericShowSum ::
  (Tag st) =>
  Pi st (Const String) ->
  (x -> Sigma st family') ->
  (forall i. st i -> family' i -> String) ->
  x ->
  String
genericShowSum pi f g x = mashPiSigma pi (f x) $ \t (Const conName) field ->
  conName ++ " " ++ g t field

showSum :: Sum -> String
showSum = genericShowSum sumConNames sumToGeneric (\t -> forallCSumTag @Show t show . getSumFamily)

example :: IO ()
example = mapM_ (putStrLn . showSum) [A 1, B True, C 'x']
