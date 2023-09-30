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
  ( -- * Converting between value and type level

    -- | An index can be moved between the type level and the value
    -- level.
    toValue,
    toType,
    TypeOfKind (..),

    -- * Type equality
    eqT,

    -- * Random bits
    Index (..),
    knowAll,
    Known (..),
    toValue,
    Dict (Dict),

    -- ** Consistency check
    roundTripTypeValue,
    roundTripValueType,
  )
where

import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy (Proxy))
import Type.Reflection ((:~:))

-- Library

-- | @eq \@i \@i'@ determines whether the type indices @i@ and @i'@
-- are equal, and if so returns @(i :~: i')@ which allows you to write
-- code that depends on them being equal.
--
-- @
-- case eqT @i @i' of
--    Nothing -> ... not equal ...
--    Just Refl -> ... use i and i' as though they were equal ...
-- @
eqT ::
  forall (t :: Type) (i :: t) (i' :: t).
  (Index t, Known i, Known i') =>
  -- | _
  Maybe (i :~: i')
eqT = eqT' Proxy Proxy

-- | @knowAll@ says that if we know @c (f i)@ for each @i :: t@
-- separately (@Forall t c f@) then we know @c (f i)@ for all @i@ at
-- once (@Known i => Dict (c (f i))@).
knowAll ::
  forall (t :: Type) (i :: t) c f.
  (Index t) =>
  (Forall t c f) =>
  -- | _
  ((Known i) => Dict (c (f i)))
knowAll = knowAll' @t (Proxy @i) (Proxy @c) (Proxy @f)

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

  -- | @Forall t c f@ says that we know @c (f i)@ for all types @i@ of
  -- kind @t@ separately.  'knowAll' allows us to know them all at
  -- once.
  --
  -- @
  -- Forall T Eq f = (Eq (f A), Eq (f B), Eq (f C))
  -- @
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
    Proxy i ->
    Proxy c ->
    -- | _
    Proxy f ->
    ((Known i) => Dict (c (f i)))

  -- | Convert a value level index to a type level index.
  --
  -- @
  -- toType A = TypeIs (Proxy :: Proxy @A)
  -- @
  toType ::
    -- | Take a value level index (i.e. a value of type @t@)
    t ->
    -- | return it at the type level as a type of kind @t@
    TypeOfKind t

data Dict c where
  Dict :: (c) => Dict c

-- | Convert a type level index to a value level index. Take the type
-- level index @i@ (i.e. a type of kind @t@) and ...
--
-- @
-- toValue @A = A
-- @
toValue ::
  forall t (i :: t).
  (Index t) =>
  (Known i) =>
  -- | ... return it at the value level as a value of type @t@
  t
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
