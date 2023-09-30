{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
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
import Text.Read
  ( Read (readPrec),
  )
import Type.Reflection ((:~:))

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
class (Eq t) => Index t where
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

applyAny ::
  forall t r.
  (Index t) =>
  -- | _
  (forall (i' :: t). (Known i') => Proxy i' -> r) ->
  t ->
  r
applyAny = applyAny' Proxy

cond1 :: forall t (i :: t). (Index t, Known i) => Bool
cond1 =
  applyAny
    ( \(Proxy :: Proxy i') -> case eqT @_ @i @i' of
        Just {} -> True
        Nothing -> False
    )
    (toVal (know @_ @i))

cond2 :: forall t. (Index t) => t -> Bool
cond2 i = applyAny (\(Proxy :: Proxy i) -> i == toVal (know @_ @i)) i
