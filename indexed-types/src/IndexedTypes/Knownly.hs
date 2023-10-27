{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module IndexedTypes.Knownly (Matchably (Matchably)) where

import Data.Coerce (coerce)
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

instance
  (Generic (k i), Forall t (OnRep GShow0 k), Matchable i) =>
  Show (Matchably (k i))
  where
  showsPrec p =
    coerce
      @(k i -> ShowS)
      (withMatchable @_ @i @(OnRep GShow0 k) gshowsPrec p)

instance
  (Generic (k i), Forall t (OnRep GRead0 k), Matchable i) =>
  Read (Matchably (k i))
  where
  readPrec =
    coerce
      @(ReadPrec (k i))
      (withMatchable @_ @i @(OnRep GRead0 k) greadPrec)

instance
  (Generic (k i), Forall t (OnRepUnit Eq k), Matchable i) =>
  Eq (Matchably (k i))
  where
  (==) =
    coerce
      @(k i -> k i -> Bool)
      (withMatchable @_ @i @(OnRepUnit Eq k) geq)

instance
  (Generic (k i), Eq (Matchably (k i)), Forall t (OnRepUnit Ord k), Matchable i) =>
  Ord (Matchably (k i))
  where
  compare =
    coerce
      @(k i -> k i -> Ordering)
      (withMatchable @_ @i @(OnRepUnit Ord k) gcompare)

withMatchable ::
  forall (t :: Type) (i :: t) (c :: t -> Constraint) r.
  (Matchable i, Forall t c) =>
  -- | _
  ((c i) => r) ->
  -- | _
  r
withMatchable r = case matchableInAll @i of Dict -> r
