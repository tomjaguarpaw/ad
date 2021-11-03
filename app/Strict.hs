{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}

module Strict
  ( Strict
  , pattern Strict
  , strict
  ) where

import Unsafe.Coerce

class Strictly a where
  data Strict a
  strict :: a -> Strict a
  unstrict :: Strict a -> a

instance Strictly (a, b) where
  data Strict (a, b) = StrictPair' !a !b deriving Show
  strict x = unsafeCoerce $ case x of
    (!_, !_) -> x
  unstrict (StrictPair' a b) = (a, b)

instance Strictly (Maybe a) where
  data Strict (Maybe a) = StrictNothing' | StrictJust' !a deriving Show
  strict x = unsafeCoerce $ case x of
    Nothing -> x
    Just !_ -> x
  unstrict = \case
    StrictJust' j  -> Just j
    StrictNothing' -> Nothing

pattern Strict x <- (unstrict->x)

{-# COMPLETE Strict :: Strict #-}
