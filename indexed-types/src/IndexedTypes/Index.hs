{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-duplicate-exports #-}

module IndexedTypes.Index
  ( Index (..),
    eqT,
    withKnown,
    coerceMethod,
    Known (..),
    toValue,
    Dict (..),

    -- * Converting between value and type level
    toValue,
    TypeOfKind (..),
    toType,

    -- ** Consistency check
    roundTripTypeValue,
    roundTripValueType,
  )
where

import Data.Coerce (Coercible, coerce)
import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy (Proxy))
import Type.Reflection ((:~:))

-- Library

-- | @eq \@i \@i'@ determines whether the type indices @i@ and @i'@
-- are equal, and if so returns @(i :~: i')@ which allows you to write
-- code that depends on them being equal.
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
withKnown r = case knowAll' @t (Proxy @i) (Proxy @c) (Proxy @f) of
  Dict -> r

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

-- | All the stuff you need for type @t@ to be an "index type".  For
-- example @data T = A | B | C@.
type Index :: Type -> Constraint
class (Eq t) => Index t where
  -- | @
  -- type Singleton T i where
  --   SA :: ST A
  --   SB :: SB B
  --   SC :: SC C
  -- @
  data Singleton t :: t -> Type

  type Forall t (c :: Type -> Constraint) (f :: t -> Type) :: Constraint

  -- | Use 'eqT' instead, except when defining this class.
  eqT' ::
    forall (i :: t) (i' :: t).
    (Known i, Known i') =>
    -- | _
    Proxy i ->
    Proxy i' ->
    Maybe (i :~: i')

  -- | From this we derive 'toValue'.
  singletonToValue :: Singleton t i -> t

  -- | Not sure why this requires Proxy arguments
  --
  -- The implementation of @knowAll'@ is implicitly a check that
  -- @'Forall' t@ is correct
  knowAll' ::
    (Forall t c f) =>
    (Known i) =>
    Proxy i ->
    Proxy c ->
    -- | _
    Proxy f ->
    Dict (c (f i))

  -- | Take the value level index @i@ (i.e. a value of type @t@) and
  -- return it at the type level as a type of kind @t@.
  toType :: t -> TypeOfKind t

data Dict c where
  Dict :: (c) => Dict c

-- | Take the type level index @i@ (i.e. a type of kind @t@) and
-- return it at the value level as a value of type @t@.
toValue :: forall t (i :: t). (Known i, Index t) => t
toValue = singletonToValue (know @_ @i)

-- | One of the 'Known' types, @i@, of kind @t@.  You can get @i@ by
-- pattern matching, for example
--
-- @
-- \case (TypeIs (Proxy :: Proxy i)) -> ...
-- @
--
-- and then you can proceed to use @i@ as a 'Known' type of kind @t@.
data TypeOfKind t where
  TypeIs :: forall t i. (Known (i :: t)) => Proxy i -> TypeOfKind t

roundTripTypeValue :: forall t (i :: t). (Index t, Known i) => Bool
roundTripTypeValue =
  case toType (toValue @_ @i) of
    TypeIs (Proxy :: Proxy i') -> case eqT @_ @i @i' of
      Just {} -> True
      Nothing -> False

roundTripValueType :: forall t. (Index t) => t -> Bool
roundTripValueType i =
  case toType i of TypeIs (Proxy :: Proxy i') -> i == toValue @_ @i'
