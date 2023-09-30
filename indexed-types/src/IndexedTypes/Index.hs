{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

module IndexedTypes.Index where

import Data.Coerce (Coercible, coerce)
import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy (Proxy))
import GHC.Read (expectP, paren)
import Text.Read
  ( Lexeme (Punc),
    Read (readPrec),
    ReadPrec,
    parens,
  )
import Type.Reflection ((:~:) (Refl))

-- Library

-- | @eq \@i \@i'@ determines whether the type indices @i@ and @i'@ are
-- equal.
eqT ::
  forall (t :: Type) (i :: t) (i' :: t).
  (Index t, Known i, Known i') =>
  -- | _
  Maybe (i :~: i')
eqT = eqT' Proxy Proxy

withKnown ::
  forall (t :: Type) (i :: t) c f r.
  (Known i, Index t, Forall t c f) =>
  -- | _
  ((c (f i)) => r) ->
  -- | _
  r
withKnown = withKnown' @t (Proxy @i) (Proxy @c) (Proxy @f)

coerceMethod ::
  forall (t :: Type) (i :: t) (c :: Type -> Constraint) f a2 a3.
  () =>
  (Index t) =>
  (Forall t c f) =>
  (Known i) =>
  (Coercible a2 a3) =>
  ((c (f i)) => a2) ->
  -- | _
  a3
coerceMethod a2 = coerce @a2 @a3 (withKnown @t @i @c @f a2)

type Known :: forall t. t -> Constraint
class Known (i :: t) where
  know :: Singleton t i

type Index :: Type -> Constraint
class Index t where
  data Singleton t :: t -> Type

  type Forall t (c :: Type -> Constraint) (f :: t -> Type) :: Constraint

  eqT' ::
    forall (i :: t) (i' :: t).
    (Known i, Known i') =>
    -- | _
    Proxy i ->
    Proxy i' ->
    Maybe (i :~: i')

  toVal :: Singleton t i -> t

  -- Not sure why this requires Proxy arguments
  --
  -- withKnown' is implicitly a check that Forall t is correct
  withKnown' ::
    Proxy i ->
    Proxy c ->
    -- | _
    Proxy f ->
    (Known i, Forall t c f) =>
    ((c (f i)) => r) ->
    r

  -- applyAny' is implicitly a check that all the values of t are
  -- Known.
  applyAny' ::
    -- | _
    Proxy i ->
    (forall (i' :: t). (Known i') => Proxy i' -> r) ->
    t ->
    r

newtype Knownly a = Knownly a

instance (Known i, Forall t Show k, Index t) => Show (Knownly (k i)) where
  show = coerceMethod @t @i @Show @k (show @(k i))

instance (Known i, Forall t Read k, Index t) => Read (Knownly (k i)) where
  readPrec = coerceMethod @t @i @Read @k (readPrec @(k i))

instance (Known i, Forall t Eq k, Index t) => Eq (Knownly (k i)) where
  (==) = coerceMethod @t @i @Eq @k ((==) @(k i))

instance
  (Known i, Forall t Ord k, Index t, Eq (Knownly (k i))) =>
  Ord (Knownly (k i))
  where
  compare = coerceMethod @t @i @Ord @k (compare @(k i))

data Some k where
  Some :: (Known t) => k t -> Some k

instance
  forall (t :: Type) (k :: t -> Type).
  (Show t, Index t, forall (i :: t). (Known i) => Show (k i)) =>
  Show (Some k)
  where
  -- In later GHCs this is
  --
  --   show (Some @i v) = ...
  show (Some (v :: k i)) = show (toVal (know @_ @i), v)

instance
  forall (t :: Type) (k :: t -> Type).
  (forall i. (Known i) => Eq (k i), Index t) =>
  Eq (Some k)
  where
  -- In later GHCs this is
  --
  --   Some @i1 v1 == Some @i2 v2 = ...
  Some (v1 :: k i1) == Some (v2 :: k i2) = case eqT @_ @i1 @i2 of
    Just Refl -> v1 == v2
    Nothing -> False

applyAny ::
  forall t r.
  (Index t) =>
  -- | _
  (forall (i' :: t). (Known i') => Proxy i' -> r) ->
  t ->
  r
applyAny = applyAny' Proxy

instance
  forall (t :: Type) (k :: t -> Type).
  (forall i. (Known i) => Read (k i), Read t, Index t) =>
  Read (Some k)
  where
  readPrec = wrap_tup $ do
    i <- readPrec
    read_comma
    applyAny (\(Proxy :: Proxy i') -> Some @i' <$> readPrec) i

-- Example to show that it works

-- These ReadPrec combinators are borrowed from
--
-- https://hackage.haskell.org/package/base-4.18.1.0/docs/src/GHC.Read.html#line-681

-- * Not for export

wrap_tup :: ReadPrec a -> ReadPrec a
wrap_tup p = parens (paren p)

read_tup2 :: (Read a, Read b) => ReadPrec (a, b)
-- Reads "a , b"  no parens!
read_tup2 = do
  x <- readPrec
  read_comma
  y <- readPrec
  return (x, y)

read_comma :: ReadPrec ()
read_comma = expectP (Punc ",")
