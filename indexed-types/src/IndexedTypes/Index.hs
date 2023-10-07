{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
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

    -- ** Type level to value level
    toValue,
    constructor,

    -- ** Value level to type level
    toType,
    AsKind (AsType),
    asType,

    -- * Type equality
    eqT,

    -- * @Index@ class
    Index (Constructor, All, eqT', constructorToValue, matchableInAll', toType),

    -- * @Forall@
    Forall,

    -- * @Matchable@ class
    Matchable (constructor'),

    -- * Equivalence between @Matchable@ and @InAll@

    -- | We can freely convert between 'Matchable' and 'InAll'.  In
    -- other words we can freely convert between a @Matchable@
    -- constraint and a collection of constraints, one for each
    -- element of @t@.
    matchableInAll,
    allMatchable,

    -- * Dict
    Dict (Dict),

    -- * @TypeOf@

    -- | Using @TypeOf@ is a hack to make the type arguments to
    -- several functions simpler.  @TypeOf i ~ t@ just means @i :: t@.
    -- Using @TypeOf@ allows us to make the kind of @i@ an invisible
    -- type argument so we don't have to explicitly avoid specifying
    -- it with @\@_@, the omitted type argument.  Future versions of
    -- GHC will allow explicitly marking type arguments as "invisible"
    -- and this hack won't be needed under those GHCs.
    TypeOf,

    -- * @InAll@

    -- | @InAll (i :: t)@ is defined to be the constraint
    --
    -- @
    -- (forall (c :: t -> Constraint). Forall t c => c i, Index t)
    -- @
    --
    -- which holds exactly when @t@ is an 'Index' type and @i@ occurs
    -- among the elements of @'All' t@.
    InAll,
  )
where

import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy (Proxy))

-- | Convert a type level index to a value level index. Take the type
-- level index @i@ (i.e. a type of kind @t@) and return it at the
-- value level (i.e. as a value of type @t@).
--
-- @
-- toValue \@A = A
-- toValue \@B = B
-- toValue \@C = C
-- @
toValue :: forall i. (Matchable i) => TypeOf i
toValue = constructorToValue (constructor @i)

-- | One of the 'Matchable' types, @i@, of kind @t@.  You can get @i@ by
-- pattern matching:
--
-- @
-- case toType t of
--   AsType (_ :: Proxy i) -> ...
-- @
--
-- (We need the @Proxy@ field only because GHC 9.0 and earlier can't
-- bind type variables in patterns.)
data AsKind t where
  AsType :: forall t (i :: t). (Matchable i) => Proxy i -> AsKind t

-- | Construct an 'AsKind'.  Simpler alternative to 'AsType'.
--
-- @
-- case (asType @A) of
--   AsType (_ :: Proxy i) -> ... here i will be A ...
-- @
--
-- >>> case (asType @A) of AsType (_ :: Proxy i) -> toValue @i
-- A
asType :: forall i. (Matchable i) => AsKind (TypeOf i)
asType = AsType @_ @i Proxy

-- | @eq \@i \@i'@ determines whether the type indices @i@ and @i'@
-- are equal, and if so returns @Dict (i ~ i')@, which allows you to
-- write code that depends on them being equal.
--
-- @
-- case eqT \@i \@i' of
--    Nothing -> ... i and i' are not equal ...
--    Just Dict -> ... here we can use that i ~ i' ...
-- @
--
-- Indices should be equal at the type level if and only if they are
-- equal at the value level.  'IndexedTypes.Consistency.eqEquality'
-- checks that propery.
eqT ::
  forall i i'.
  (Matchable i, Matchable i', TypeOf i ~ TypeOf i') =>
  -- | _
  Maybe (Dict (i ~ i'))
eqT = eqT' Proxy Proxy

type Index :: Type -> Constraint
class (Eq t) => Index t where
  -- | @
  -- data Constructor i where
  --   SA :: Constructor A
  --   SB :: Constructor B
  --   SC :: Constructor C
  -- @
  data Constructor :: t -> Type

  -- | All the elements of @t@, at the type level.
  --
  -- @
  -- All T = [A, B, C]
  -- @
  type All t :: [t]

  -- | The class method version of 'eqT'.  Always prefer to use 'eqT'
  -- instead, except when defining this class.
  --
  -- (@eqT'@ only has @Proxy@ arguments because it seems to be hard to
  -- bind the type arguments @i@ and @i'@ without them.  Future
  -- versions of GHC will allow to bind type variables in function
  -- definitions, making the @Proxy@s redundant.)
  eqT' ::
    forall (i :: t) (i' :: t).
    (Matchable i, Matchable i') =>
    -- | _
    Proxy i ->
    Proxy i' ->
    Maybe (Dict (i ~ i'))

  -- | This is rarely used directly, but from it we derive 'toValue'.
  --
  -- @
  -- constructorToValue = \\case SA -> A; SB -> B; SC -> C
  -- @
  --
  -- See 'Constructor' for the definition of @SA@, @SB@, @SC@.
  constructorToValue :: Constructor (i :: t) -> t

  -- | The class method version of 'matchableInAll'.  Always prefer to use
  -- 'matchableInAll' instead, except when defining this class.
  --
  -- The implementation of @matchableInAll'@ is implicitly a check that
  -- @'All' t@ is correct.
  --
  -- (@matchableInAll'@ only has a @Proxy@ argument because it seems
  -- to be hard to bind the type @i@ without it.  Future versions of
  -- GHC will allow to bind type variables in function definitions,
  -- making the @Proxy@ redundant.)
  matchableInAll' :: (Matchable (i :: t)) => Proxy i -> Dict (InAll i)

  -- | Take a value level index (i.e. a value of type @t@) and return
  -- it at the type level (i.e. as a type of kind @t@)
  --
  -- @
  -- toType A = 'AsType' (Proxy :: Proxy A) = 'asType' \@A
  -- toType B = AsType (Proxy :: Proxy B) = asType \@B
  -- toType C = AsType (Proxy :: Proxy C) = asType \@C
  -- @
  toType :: t -> AsKind t

  -- | You will almost certainly never have to use or even be aware of
  -- the existence of this method.  It says that every element of
  -- @'All' t@ has a 'Matchable' instance.  It should only ever need
  -- to be defined through its default implementation.  I'm not sure
  -- why it's needed, actually, except that 'allMatchable' seems to
  -- rely on it.
  forallMatchable :: Dict (Forall t Matchable)
  default forallMatchable :: (For t Matchable (All t)) => Dict (Forall t Matchable)
  forallMatchable = Dict

-- | @Forall t c f@ says that we know @c (f i)@ for all types @i@ of
-- kind @t@ separately.  'matchableInAll' allows us to know them all at
-- once.
--
-- @
-- Forall T c = (c A, c B, c C)
-- @
type Forall :: forall (t :: Type) -> (t -> Constraint) -> Constraint
type Forall t c = For t c (All t)

type For :: forall (t :: Type) -> (t -> Constraint) -> [t] -> Constraint
type family For t c is where
  For _ _ '[] = ()
  For t c (i : is) = (c i, For t c is)

class
  (forall (c :: t -> Constraint). (Forall t c) => c i, Index t) =>
  InAll (i :: t)

instance
  (forall (c :: t -> Constraint). (Forall t c) => c i, Index t) =>
  InAll (i :: t)

-- | @matchableInAll@ says that we can convert code depending on a class
-- instance for @T@ into code that depends on 'Matchable'.  @T@.  That is,
-- code like
--
-- @
-- class K (i :: T) where
--   f :: ftype
--
-- instance K A where
--   f = fbodyA
--
-- instance K B where
--   f = fbodyB
--
-- instance K C where
--   f = fbodyC
-- @
--
-- can be converted to a function with a 'Matchable' constraint.
--
-- @
-- f :: Matchable i => ftype
-- f = case matchableInAll \@i of
--       Dict ->
--         case constructor \@i of
--           SA -> case c @A of Dict -> f @A
--           SB -> case c @B of Dict -> f @B
--           SC -> case c @C of Dict -> f @C
-- @
matchableInAll :: forall i. (Matchable i) => Dict (InAll i)
matchableInAll = matchableInAll' @(TypeOf i) Proxy

allMatchable :: forall i. (InAll i) => Dict (Matchable i)
allMatchable = case forallMatchable @(TypeOf i) of Dict -> Dict

type Matchable :: forall t. t -> Constraint
class (Index t) => Matchable (i :: t) where
  constructor' :: Constructor i

type TypeOf :: k -> Type
type TypeOf (i :: t) = t

-- | Convert a type level index to a value.  This is more powerful
-- than 'toValue' because when we pattern match on the result we can
-- use use the value of the type level index in body of the @case@
-- branch.
--
-- @
-- constructor \@A = SA
-- constructor \@B = SB
-- constructor \@B = SC
-- @
--
-- @
-- case constructor @i of
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
-- See 'Constructor' for the definition of @SA@, @SB@, @SC@.
constructor :: forall i. (Matchable i) => Constructor i
constructor = constructor'

data Dict c where
  Dict :: (c) => Dict c
