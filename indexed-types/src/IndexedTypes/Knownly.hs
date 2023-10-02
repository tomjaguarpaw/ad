{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

module IndexedTypes.Knownly (Knownly (Knownly)) where

import Data.Coerce (Coercible, coerce)
import Data.Kind (Constraint, Type)
import IndexedTypes.Index (Dict (Dict), Index (Forall), Known, knowAll)
import Text.Read (Read (readPrec))

-- | Knownly is a @newtype@ that exists to allow deriving of instances
-- for indexed types.  See "IndexedTypes.Example" for an example.
newtype Knownly a = Knownly a

instance (Known i, Forall t Type Show k) => Show (Knownly (k i)) where
  show = coerceMethod @t @i @_ @Show @k (show @(k i))

instance (Known i, Forall t Type Read k) => Read (Knownly (k i)) where
  readPrec = coerceMethod @t @i @_ @Read @k (readPrec @(k i))

instance (Known i, Forall t Type Eq k) => Eq (Knownly (k i)) where
  (==) = coerceMethod @t @i @_ @Eq @k ((==) @(k i))

instance
  (Known i, Eq (Knownly (k i)), Forall t Type Ord k) =>
  Ord (Knownly (k i))
  where
  compare = coerceMethod @t @i @_ @Ord @k (compare @(k i))

withKnown ::
  forall (t :: Type) (i :: t) k c f r.
  (Known i, Forall t k c f) =>
  -- | _
  ((c (f i)) => r) ->
  -- | _
  r
withKnown r = case knowAll @t @i @_ @c @f of Dict -> r

coerceMethod ::
  forall (t :: Type) (i :: t) k (c :: k -> Constraint) f a2 a3.
  () =>
  (Forall t k c f) =>
  (Known i) =>
  (Coercible a2 a3) =>
  ((c (f i)) => a2) ->
  -- | _
  a3
coerceMethod a2 = coerce @a2 @a3 (withKnown @t @i @_ @c @f a2)
