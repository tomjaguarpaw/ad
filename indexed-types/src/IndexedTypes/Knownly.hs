{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module IndexedTypes.Knownly
  ( Matchably (Matchably),
    Matchably' (Matchably'),
  )
where

import Data.Coerce (Coercible, coerce)
import Data.Kind (Constraint, Type)
import GHC.Generics (Rep)
import Generic.Data
  ( GRead0,
    GShow0,
    Generic,
    gcompare,
    geq,
    greadPrec,
    gshowsPrec,
  )
import IndexedTypes.Index (Dict (Dict), Forall, Matchable, matchableInAll)
import Text.Read (Read (readPrec), ReadPrec)

-- | Matchably is a @newtype@ that exists to allow deriving of instances
-- for indexed types.  See "IndexedTypes.Example" for an example.
newtype Matchably a = Matchably a

newtype Matchably' c a = Matchably' a

class (c (f i)) => Compose c f i

instance (c (f i)) => Compose c f i

type OnRep ::
  forall (t :: Type).
  ((Type -> Type) -> Constraint) ->
  (t -> Type) ->
  t ->
  Constraint
class (c (Rep (k i))) => OnRep c k i

instance (c (Rep (k i))) => OnRep c k i

type OnRepUnit ::
  forall (t :: Type).
  (Type -> Constraint) ->
  (t -> Type) ->
  t ->
  Constraint
class (c (Rep (k i) ())) => OnRepUnit c k i

instance (c (Rep (k i) ())) => OnRepUnit c k i

-- Sadly this only works in >= 9.4 because of some issue to do with
-- using the quantified constraint.
cshowsPrec ::
  forall (t :: Type) (a :: Type) (k :: t -> Type) (i :: t) (c :: t -> Constraint).
  ( Matchable i,
    Forall t c,
    Generic (k i),
    forall i'. (c i') => OnRep GShow0 k i',
    Coercible a (k i)
  ) =>
  Int ->
  a ->
  ShowS
cshowsPrec p =
  coerce
    @(k i -> ShowS)
    (withMatchable @t @i @c gshowsPrec p)

instance
  forall (t :: Type) (k :: t -> Type) (i :: t) (c :: t -> Constraint).
  ( Generic (k i),
    Forall t c,
    forall i'. (c i') => OnRep GShow0 k i',
    Matchable i
  ) =>
  Show (Matchably' c (k i))
  where
  showsPrec = cshowsPrec @t @(Matchably' c (k i)) @k @i @c

instance
  ( Generic (k i),
    Forall t c,
    forall i'. (c i') => OnRep GRead0 k i',
    Matchable i
  ) =>
  Read (Matchably' c (k i))
  where
  readPrec =
    coerce
      @(ReadPrec (k i))
      (withMatchable @_ @i @c greadPrec)

instance
  ( Generic (k i),
    Forall t c,
    forall i'. (c i') => OnRepUnit Eq k i',
    Matchable i
  ) =>
  Eq (Matchably' c (k i))
  where
  (==) =
    coerce
      @(k i -> k i -> Bool)
      (withMatchable @_ @i @c geq)

instance
  ( Generic (k i),
    Forall t c,
    forall i'. (c i') => OnRepUnit Ord k i',
    forall i'. (c i') => OnRepUnit Eq k i',
    Matchable i
  ) =>
  Ord (Matchably' c (k i))
  where
  compare =
    coerce
      @(k i -> k i -> Ordering)
      (withMatchable @_ @i @c gcompare)

deriving via
  (Matchably' (OnRep GShow0 k) (k (i :: t)))
  instance
    (Forall t (OnRep GShow0 k), Generic (k i), Matchable i) =>
    Show (Matchably (k i))

deriving via
  (Matchably' (OnRep GRead0 k) (k (i :: t)))
  instance
    (Forall t (OnRep GRead0 k), Generic (k i), Matchable i) =>
    Read (Matchably (k i))

deriving via
  (Matchably' (OnRepUnit Eq k) (k (i :: t)))
  instance
    (Forall t (OnRepUnit Eq k), Generic (k i), Matchable i) =>
    Eq (Matchably (k i))

deriving via
  (Matchably' (OnRepUnit Ord k) (k (i :: t)))
  instance
    (Forall t (OnRepUnit Eq k), Forall t (OnRepUnit Ord k), Generic (k i), Matchable i) =>
    Ord (Matchably (k i))

withMatchable ::
  forall (t :: Type) (i :: t) (c :: t -> Constraint) r.
  (Matchable i, Forall t c) =>
  -- | _
  ((c i) => r) ->
  -- | _
  r
withMatchable r = case matchableInAll @i of Dict -> r
