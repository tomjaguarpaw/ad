{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

module IndexedTypes.Knownly where

import IndexedTypes.Index (Index (Forall), Known, coerceMethod)
import Text.Read (Read (readPrec))

newtype Knownly a = Knownly a

instance (Known i, Index t, Forall t Show k) => Show (Knownly (k i)) where
  show = coerceMethod @t @i @Show @k (show @(k i))

instance (Known i, Index t, Forall t Read k) => Read (Knownly (k i)) where
  readPrec = coerceMethod @t @i @Read @k (readPrec @(k i))

instance (Known i, Index t, Forall t Eq k) => Eq (Knownly (k i)) where
  (==) = coerceMethod @t @i @Eq @k ((==) @(k i))

instance
  (Known i, Index t, Eq (Knownly (k i)), Forall t Ord k) =>
  Ord (Knownly (k i))
  where
  compare = coerceMethod @t @i @Ord @k (compare @(k i))
