{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}

module Strict
  ( pattern Strict
  , Strictly(strict, unstrict, matchStrict)
  , Strict
  ) where

import Unsafe.Coerce

class Strictly a where
  data Strict a
  -- | @
  -- makeStrict :: Int -> Strict (Int, String)
  -- makeStrict i = strict (i + 1, show i)
  -- @
  strict :: a -> Strict a
  -- | Used to implement the @Strict@ pattern synonym.
  matchStrict :: Strict a -> a
  -- | @
  -- strictMaybe :: r -> (a -> r) -> Strict (Maybe a) -> r
  -- strictMaybe r f sm = maybe r f (unstrict sm)
  -- @
  unstrict :: Strict a -> a
  unstrict = unsafeCoerce

instance Strictly (a, b) where
  data Strict (a, b) = StrictPair' !a !b deriving Show
  strict x = unsafeCoerce $ case x of
    (!_, !_) -> x
  matchStrict (StrictPair' a b) = (a, b)
  unstrict = unsafeCoerce

instance Strictly (Maybe a) where
  data Strict (Maybe a) = StrictNothing' | StrictJust' !a deriving Show
  strict x = unsafeCoerce $ case x of
    Nothing -> x
    Just !_ -> x
  matchStrict = \case
    StrictJust' j  -> Just j
    StrictNothing' -> Nothing
  unstrict = unsafeCoerce

-- | @
-- printIt :: Strict (Maybe Int) -> IO ()
-- printIt (Strict (Just i)) = print i
-- printIt (Strict Nothing)  = putStrLn "Nothing there"
-- @
pattern Strict :: Strictly a => a -> Strict a
pattern Strict x <- (matchStrict->x)

{-# COMPLETE Strict :: Strict #-}
