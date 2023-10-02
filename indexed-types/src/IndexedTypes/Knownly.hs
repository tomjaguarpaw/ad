{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE TypeFamilies #-}

module IndexedTypes.Knownly (Knownly (Knownly)) where

import Data.Coerce (Coercible, coerce)
import Data.Kind (Type)
import IndexedTypes.Index (Forall, Known, knowAll, Contains (Contains))
import Text.Read (Read (readPrec))

-- | Knownly is a @newtype@ that exists to allow deriving of instances
-- for indexed types.  See "IndexedTypes.Example" for an example.
newtype Knownly a = Knownly a

class c (f i) => Compose c f i where

instance Show (f i) => Compose Show f i where

instance Read (f i) => Compose Read f i where

instance Eq (f i) => Compose Eq f i where

instance Ord (f i) => Compose Ord f i where

instance (Known i, Forall t (Compose Show k)) => Show (Knownly (k i)) where
  show = coerceMethod @t @i @(Compose Show k) (show @(k i))

instance (Known i, Forall t (Compose Read k)) => Read (Knownly (k i)) where
  readPrec = coerceMethod @t @i @(Compose Read k) (readPrec @(k i))

instance (Known i, Forall t (Compose Eq k)) => Eq (Knownly (k i)) where
  (==) = coerceMethod @t @i @(Compose Eq k) ((==) @(k i))

instance
  (Known i, Eq (Knownly (k i)), Forall t (Compose Ord k)) =>
  Ord (Knownly (k i))
  where
  compare = coerceMethod @t @i @(Compose Ord k) (compare @(k i))

withKnown ::
  forall (t :: Type) (i :: t) c r.
  (Known i, Forall t c) =>
  -- | _
  ((c i) => r) ->
  -- | _
  r
withKnown r = case knowAll @t @i of Contains -> r

coerceMethod ::
  forall (t :: Type) (i :: t) c a2 a3.
  () =>
  (Forall t c) =>
  (Known i) =>
  (Coercible a2 a3) =>
  ((c i) => a2) ->
  -- | _
  a3
coerceMethod a2 = coerce @a2 @a3 (withKnown @t @i @c a2)
