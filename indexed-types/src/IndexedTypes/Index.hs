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

-- | This module contains everything you need to define an index type.
-- Then you can work with types indexed by your index types ("indexed
-- types").  The benefit of this particular implementation is that
-- instances for indexed types are easily derivable.  For a full
-- example implementation see "IndexedTypes.Example".
--
-- The documentation gives example implementations for a small index
-- type @data T = A | B | C@.
module IndexedTypes.Index
  ( -- * Converting between value and type level

    -- | An index can be moved between the type level and the value
    -- level.  You might expect that @toValue@ and @toType@ should be
    -- inverses, and indeed they should!
    -- 'IndexedTypes.Consistency.roundTripTypeValue' and
    -- 'IndexedTypes.Consistency.roundTripValueType' are automated
    -- checks of that property.

    -- * Type level to value level
    toValue,
    know,

    -- * Value level to type level
    toType,
    AsKind (AsType),

    -- * Type equality
    eqT,

    -- * @Index@ class
    Index (..),

    -- * @Known@ class
    Known (know'),

    -- * @knowAll@: converting separate constraints to a 'Known' constraint
    knowAll,

    -- * Dict
    Dict (Dict),

    -- * @TypeOf@

    -- | Using @TypeOf@ is a hack to make the type arguments to
    -- several functions simpler.  @t ~ TypeOf i@ just means @t :: i@.
    -- Using @TypeOf@ allows us to make the kind of @i@ an invisible
    -- type argument so we don't have to explicitly avoid specifying
    -- it with @\@_@, the omitted type argument.  Future versions of
    -- GHC will allow explicitly marking type arguments as "invisible"
    -- and this hack won't be needed under those GHCs.
    TypeOf,
  )
where

import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy (Proxy))
import Type.Reflection ((:~:))

-- | Convert a type level index to a value level index. Take the type
-- level index @i@ (i.e. a type of kind @t@) and return it at the
-- value level (i.e. as a value of type @t@).
--
-- @
-- toValue \@A = A
-- toValue \@B = B
-- toValue \@C = C
-- @
toValue :: forall i. (Known i) => TypeOf i
toValue = singletonToValue (know @i)

-- | One of the 'Known' types, @i@, of kind @t@.  You can get @i@ by
-- pattern matching:
--
-- @
-- case toType t of
--   AsType (_ :: Proxy i) -> ...
-- @
--
-- (We need the @Proxy@ field only because older versions of GHC can't
-- bind type variables in patterns.)
data AsKind t where
  AsType :: forall t i. (Known (i :: t)) => Proxy i -> AsKind t

-- | @eq \@i \@i'@ determines whether the type indices @i@ and @i'@
-- are equal, and if so returns @(i :~: i')@, which allows you to write
-- code that depends on them being equal.
--
-- @
-- case eqT @i @i' of
--    Nothing -> ... i and i' are not equal ...
--    Just Refl -> ... here we can use that i ~ i' ...
-- @
--
-- Indices should be equal at the type level if and only if they are
-- equal at the value level.  'IndexedTypes.Consistency.eqEquality'
-- checks that propery.
eqT ::
  forall i i'.
  (Known i, Known i', TypeOf i ~ TypeOf i') =>
  -- | _
  Maybe (i :~: i')
eqT = eqT' Proxy Proxy

type Index :: Type -> Constraint
class (Eq t) => Index t where
  -- | @
  -- type Singleton T i where
  --   SA :: ST A
  --   SB :: SB B
  --   SC :: SC C
  -- @
  data Singleton :: t -> Type

  -- | @Forall t c f@ says that we know @c (f i)@ for all types @i@ of
  -- kind @t@ separately.  'knowAll' allows us to know them all at
  -- once.
  --
  -- @
  -- Forall T Eq f = (Eq (f A), Eq (f B), Eq (f C))
  -- @
  type Forall t k (c :: k -> Constraint) (f :: t -> k) :: Constraint

  -- | The class method version of 'eqT'.  Always prefer to use 'eqT'
  -- instead, except when defining this class.
  --
  -- (@eqT'@ only has @Proxy@ arguments because it seems to be hard to
  -- bind the type arguments @i@ and @i'@ without them.  Future
  -- versions of GHC will allow to bind type variables in function
  -- definitions, making the @Proxy@s redundant.)
  eqT' ::
    forall (i :: t) (i' :: t).
    (Known i, Known i') =>
    -- | _
    Proxy i ->
    Proxy i' ->
    Maybe (i :~: i')

  -- | This is rarely used directly, but from it we derive 'toValue'.
  --
  -- @
  -- singletonToValue = \\case SA -> A; SB -> B; SC -> C
  -- @
  --
  -- See 'Singleton' for the definition of @SA@, @SB@, @SC@.
  singletonToValue :: Singleton (i :: t) -> t

  -- | The class method version of 'knowAll'.  Always prefer to use
  -- 'knowAll' instead, except when defining this class.
  --
  -- The implementation of @knowAll'@ is implicitly a check that
  -- @'Forall' t@ is correct.
  --
  -- (@knowAll'@ only has @Proxy@ arguments because it seems to be
  -- hard to bind the type arguments @t@, @c@ and @f@ without them.
  -- Future versions of GHC will allow to bind type variables in
  -- function definitions, making the @Proxy@s redundant.)
  knowAll' ::
    (Forall t k c f) =>
    Proxy i ->
    Proxy c ->
    -- | _
    Proxy f ->
    ((Known i) => Dict (c (f i)))

  -- | Take a value level index (i.e. a value of type @t@) and return
  -- it at the type level (i.e. as a type of kind @t@)
  --
  -- @
  -- toType A = AsType (Proxy :: Proxy A)
  -- toType B = AsType (Proxy :: Proxy B)
  -- toType C = AsType (Proxy :: Proxy C)
  -- @
  toType :: t -> AsKind t

-- | @knowAll@ says that if we know @c (f i)@ for each @i :: t@
-- separately (@Forall t c f@) then we know @c (f i)@ for all @i@ at
-- once (@Known i => Dict (c (f i))@).
knowAll ::
  forall (t :: Type) (i :: t) k c f.
  (Forall t k c f) =>
  -- | _
  ((Known i) => Dict (c (f i)))
knowAll = knowAll' @t (Proxy @i) (Proxy @c) (Proxy @f)

type Known :: forall t. t -> Constraint
class (Index t) => Known (i :: t) where
  know' :: Singleton i

type TypeOf :: k -> Type
type TypeOf (i :: t) = t

-- | Convert a type level index to a value.  This is more powerful
-- than 'toValue' because when we pattern match on the result we can
-- use use the value of the type level index in body of the @case@
-- branch.
--
-- @
-- know \@A = SA
-- know \@B = SB
-- know \@B = SC
-- @
--
-- @
-- case know @i of
--   SA -> ... here we can use that i ~ A ...
--   SB -> ...                      i ~ B ...
--   SC -> ...                      i ~ C ...
-- @
--
-- @
-- case 'toValue' @i of
--   A -> ... here i ~ A but we can't use that fact ...
--   B -> ...      i ~ B                            ...
--   C -> ...      i ~ C                            ...
-- @
--
-- See 'Singleton' for the definition of @SA@, @SB@, @SC@.
know :: forall i. (Known i) => Singleton i
know = know'

data Dict c where
  Dict :: (c) => Dict c
