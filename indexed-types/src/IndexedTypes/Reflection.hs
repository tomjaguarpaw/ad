{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-duplicate-exports #-}

module IndexedTypes.Reflection
  ( -- ** Reify/reflect
    reify,
    reflect,
  )
where

import Data.Proxy (Proxy)
import IndexedTypes.Index (Index (toType), Known, TypeOfKind (TypeIs), toValue)

-- | See also e.g.
-- @Data.Reflection.@'Data.Reflection.reifyNat'.
reify ::
  (Index t) =>
  -- | Convert this value to a type
  t ->
  -- | and apply it as a type argument @i@ to this function
  (forall (i :: t). (Known i) => Proxy i -> r) ->
  r
reify t f = case toType t of
  TypeIs i -> f i

-- | Take a type argument @i@ of kind @t@ and return ...
reflect ::
  forall t (i :: t).
  (Known i, Index t) =>
  -- | @i@ as a value of type @t@
  t
reflect = toValue @_ @i
