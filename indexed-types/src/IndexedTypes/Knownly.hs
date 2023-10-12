{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module IndexedTypes.Knownly (Matchably (Matchably)) where

import Data.Coerce (Coercible, coerce)
import Data.Kind (Type)
import IndexedTypes.Index (Dict (Dict), Forall, Matchable, matchableInAll)
import Text.Read (Read (readPrec))

-- | Matchably is a @newtype@ that exists to allow deriving of instances
-- for indexed types.  See "IndexedTypes.Example" for an example.
newtype Matchably a = Matchably a

class (c (f i)) => Compose c f i

instance (Show (f i)) => Compose Show f i

instance (Read (f i)) => Compose Read f i

instance (Eq (f i)) => Compose Eq f i

instance (Ord (f i)) => Compose Ord f i

instance (Matchable i, Forall t (Compose Show k)) => Show (Matchably (k i)) where
  show = coerceMethod @_ @i @(Compose Show k) (show @(k i))

instance (Matchable i, Forall t (Compose Read k)) => Read (Matchably (k i)) where
  readPrec = coerceMethod @_ @i @(Compose Read k) (readPrec @(k i))

instance (Matchable i, Forall t (Compose Eq k)) => Eq (Matchably (k i)) where
  (==) = coerceMethod @_ @i @(Compose Eq k) ((==) @(k i))

instance
  (Matchable i, Eq (Matchably (k i)), Forall t (Compose Ord k)) =>
  Ord (Matchably (k i))
  where
  compare = coerceMethod @_ @i @(Compose Ord k) (compare @(k i))

withMatchable ::
  forall (t :: Type) (i :: t) c r.
  (Matchable i, Forall t c) =>
  -- | _
  ((c i) => r) ->
  -- | _
  r
withMatchable r = case matchableInAll @i of Dict -> r

coerceMethod ::
  forall (t :: Type) (i :: t) c a2 a3.
  () =>
  (Forall t c) =>
  (Matchable i) =>
  (Coercible a2 a3) =>
  ((c i) => a2) ->
  -- | _
  a3
coerceMethod a2 = coerce @a2 @a3 (withMatchable @t @i @c a2)
