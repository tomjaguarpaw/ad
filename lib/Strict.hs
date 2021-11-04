{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}

module Strict
  ( pattern Strict
  , Strictly(strict, unstrict, matchStrict)
  , Strict
  ) where

import Unsafe.Coerce (unsafeCoerce)
import qualified Data.Strict
import Data.These (These(This, That, These))
import GHC.TypeLits

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

instance Strictly (a, b) where
  newtype Strict (a, b) = StrictPair (Data.Strict.Pair a b) deriving Show
  strict x = unsafeCoerce $ case x of
    (!_, !_) -> x
  matchStrict (StrictPair x) = case x of
    a Data.Strict.:!: b -> (a, b)
  unstrict = unsafeCoerce

instance Strictly (Maybe a) where
  newtype Strict (Maybe a) = StrictMaybe (Data.Strict.Maybe a) deriving Show
  strict x = unsafeCoerce $ case x of
    Nothing -> x
    Just !_ -> x
  matchStrict (StrictMaybe x) = case x of
    Data.Strict.Just j  -> Just j
    Data.Strict.Nothing -> Nothing
  unstrict = unsafeCoerce

instance Strictly (Either a b) where
  newtype Strict (Either a b) = StrictEither (Data.Strict.Either a b) deriving Show
  strict x = unsafeCoerce $ case x of
    Left !_  -> x
    Right !_ -> x
  matchStrict (StrictEither x) = case x of
    Data.Strict.Left l  -> Left l
    Data.Strict.Right r -> Right r
  unstrict = unsafeCoerce

instance Strictly (These a b) where
  newtype Strict (These a b) = StrictThese (Data.Strict.These a b) deriving Show
  strict x = unsafeCoerce $ case x of
    This !_     -> x
    That !_     -> x
    These !_ !_ -> x
  matchStrict (StrictThese x) = case x of
    Data.Strict.This t    -> This t
    Data.Strict.That t    -> That t
    Data.Strict.These s t -> These s t
  unstrict = unsafeCoerce

type family AlreadyStrict t :: ErrorMessage
type instance AlreadyStrict t = 'ShowType t ':<>: 'Text " is already strict."
                                ':<>: 'Text " Just use it normally, don't wrap it in Strict."

instance TypeError (AlreadyStrict Int) => Strictly Int where
instance TypeError (AlreadyStrict Double) => Strictly Double where

-- | @
-- printIt :: Strict (Maybe Int) -> IO ()
-- printIt (Strict (Just i)) = print i
-- printIt (Strict Nothing)  = putStrLn "Nothing there"
-- @
pattern Strict :: Strictly a => a -> Strict a
pattern Strict x <- (matchStrict->x)

{-# COMPLETE Strict :: Strict #-}
