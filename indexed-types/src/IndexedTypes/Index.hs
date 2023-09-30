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

module IndexedTypes.Index where

import Data.Coerce (Coercible, coerce)
import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy (Proxy))
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

  singletonToValue :: Singleton t i -> t

  -- | Not sure why this requires Proxy arguments
  --
  -- The implementation of @withKnown'@ is implicitly a check that
  -- @'Forall' t@ is correct
  withKnown' ::
    Proxy i ->
    Proxy c ->
    -- | _
    Proxy f ->
    (Known i, Forall t c f) =>
    ((c (f i)) => r) ->
    r

  -- | The definition of @applyAny@ for an indexed type.  For some
  -- reason making this a type class method seems to require a @Proxy@
  -- argument.  In practice you should use 'applyAny' instead, which
  -- doesn't use the @Proxy@ argument.
  --
  -- The implementation of @applyAny'@ is implicitly a check that all
  -- the values of @t@ are 'Known'.
  applyAny' ::
    -- | _
    t ->
    (forall (i' :: t). (Known i') => Proxy i' -> r) ->
    r

  -- | Take the value level index @i@ (i.e. a value of type @t@) and
  -- return it at the type level as a type of kind @t@.
  toType :: t -> TypeOfKind t

-- | Take an index (i.e. a value of type @t@) and pass it as a type
-- level argument to a function which expects an index at the type
-- level.
--
-- In other places this is called "reify", for example in
-- @Data.Reflection.@'Data.Reflection.reifyNat'.
applyAny ::
  forall t r.
  (Index t) =>
  -- | An index at the value level.
  t ->
  -- | Function expecting an index at the type level.
  (forall (i :: t). (Known i) => Proxy i -> r) ->
  r
applyAny = applyAny'

-- | Take the type level index @i@ (i.e. a type of kind @t@) and
-- return it at the value level as a value of type @t@.
toValue :: forall t (i :: t). (Known i, Index t) => t
toValue = singletonToValue (know @_ @i)

data TypeOfKind t where
  TypeIs :: forall t i. (Known (i :: t)) => TypeOfKind t

cond1 :: forall t (i :: t). (Index t, Known i) => Bool
cond1 =
  applyAny
    (toValue @_ @i)
    ( \(Proxy :: Proxy i') -> case eqT @_ @i @i' of
        Just {} -> True
        Nothing -> False
    )

cond2 :: forall t. (Index t) => t -> Bool
cond2 i = applyAny i (\(Proxy :: Proxy i) -> i == toValue @_ @i)
