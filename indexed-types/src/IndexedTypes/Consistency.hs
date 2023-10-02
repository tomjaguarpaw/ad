{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | Much of the structure of an instance "IndexedTypes.Index" is
-- guaranteed to be correct by the type system.  Some parts are not.
-- This module implement properties that must be satisfied by some of
-- those parts.
module IndexedTypes.Consistency
  ( roundTripTypeValue,
    roundTripValueType,
    eqEquality,
  )
where

import Data.Maybe (isJust)
import Data.Proxy (Proxy (Proxy))
import IndexedTypes.Index
  ( AsKind (AsType),
    Index,
    Matchable,
    eqT,
    toType,
    toValue,
  )

-- | Check that converting a type to a value and back again gives you
-- the same type that you started with.
roundTripTypeValue :: forall t (i :: t). (Matchable i) => Bool
roundTripTypeValue =
  case toType (toValue @i) of
    AsType (Proxy :: Proxy i') -> case eqT @i @i' of
      Just {} -> True
      Nothing -> False

-- | Check that converting a value to a type and back again gives you
-- the same value that you started with.
roundTripValueType :: forall t. (Index t) => t -> Bool
roundTripValueType i =
  case toType i of AsType (Proxy :: Proxy i') -> i == toValue @i'

eqEquality :: forall t (i :: t) (i' :: t). (Matchable i, Matchable i') => Bool
eqEquality = isJust (eqT @i @i') == (toValue @i == toValue @i')
