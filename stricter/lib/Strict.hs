{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}

module Strict
  (
  -- * Strict constructor and pattern

  -- | The @Strict@ constructor and pattern are the easiest way to get
  -- started with this library.
  pattern Strict
  -- * Accessor functions

  -- | The accessor functions can be more efficient than the v'Strict'
  -- constructor and pattern in some circumstances.

  , strict
  , unstrict
  -- * Class
  , Strictly(matchStrict, constructStrict)
  , Strict
  -- * Error messages

  -- | These diagnostic error messages can appear when you try to use
  -- @Strict@ on a type that doesn't support it.
  , AlreadyStrict
  , Can'tBeStrict
  ) where

import Unsafe.Coerce (unsafeCoerce)
import GHC.TypeLits

-- | A type has a @Strictly@ instance when it has a very cheap
-- conversion to and from a strict type, @Strict a@.
class Strictly a where
  -- | Isomorphic to the type @a@, except that when it is evaulated its
  -- immediate children are evaluated too.
  data Strict a
  -- | Make a @Strict a@ using 'strict' if you obtained an @a@ from
  -- elsewhere (otherwise, if you have the components of @a@
  -- separately, then it is more efficient to use the v'Strict'
  -- constructor instead).
  --
  -- @
  -- makeStrict :: (Int, Strict (Int, String)) -> Int
  -- makeStrict (i, s) = i + f (strict s)
  -- @
  strict :: a -> Strict a
  -- | Access the contents of a @Strict a@, but not its fields, using
  -- @unstrict@ (if you want access to the fields then it is more
  -- efficient to use the v'Strict' pattern).
  --
  -- @
  -- strictMaybe :: r -> (a -> r) -> Strict (Maybe a) -> r
  -- strictMaybe r f sm = maybe r f (unstrict sm)
  -- @
  unstrict :: Strict a -> a
  -- | Used to implement the v'Strict' pattern synonym.  You should
  -- never need to use @matchStrict@ unless you are defining your own
  -- instance of @Strictly@.
  matchStrict :: Strict a -> a
  -- | Used to implement the v'Strict' constructor.  You should never
  -- need to use @constructStrict@ unless you are defining your own
  -- instance of @Strictly@.
  constructStrict :: a -> Strict a

instance Strictly (a, b) where
  -- | Hello
  data Strict (a, b) = StrictPair !a !b deriving Show
  strict x = unsafeCoerce $ case x of
    (!_, !_) -> x
  matchStrict = \case
    StrictPair a b -> (a, b)
  unstrict = unsafeCoerce
  constructStrict (x, y) = StrictPair x y

instance Strictly (Maybe a) where
  data Strict (Maybe a) = StrictNothing | StrictJust !a deriving Show
  strict x = unsafeCoerce $ case x of
    Nothing -> x
    Just !_ -> x
  matchStrict = \case
    StrictJust j  -> Just j
    StrictNothing -> Nothing
  unstrict = unsafeCoerce
  constructStrict = \case
    Just j  -> StrictJust j
    Nothing -> StrictNothing

instance Strictly (Either a b) where
  data Strict (Either a b) = StrictLeft a | StrictRight b deriving Show
  strict x = unsafeCoerce $ case x of
    Left !_  -> x
    Right !_ -> x
  matchStrict = \case
    StrictLeft l  -> Left l
    StrictRight r -> Right r
  unstrict = unsafeCoerce
  constructStrict = \case
    Left l  -> StrictLeft l
    Right r -> StrictRight r

-- | Some data types, such as 'Int' and 'Double', are already as
-- strict as they can be.  There is no need to wrap them in 'Strict'!
type family AlreadyStrict t :: ErrorMessage
type instance AlreadyStrict t = 'ShowType t ':<>: 'Text " is already strict."
                                ':<>: 'Text " Just use it normally, don't wrap it in Strict."

-- | Some data types, such as @[a]@, can't be made strict in a
-- zero-cost way.
type family Can'tBeStrict t :: ErrorMessage
type instance Can'tBeStrict t = 'ShowType t ':<>: 'Text " can't be made strict."

instance TypeError (AlreadyStrict ()) => Strictly ()
instance TypeError (AlreadyStrict Int) => Strictly Int
instance TypeError (AlreadyStrict Double) => Strictly Double

instance TypeError (Can'tBeStrict [a]) => Strictly [a]

-- | Use the @Strict@ pattern if you want to subsequently match on the
--  @a@ it contains (otherwise it is more efficient to use 'strict').
--
-- @
-- printIt :: Strict (Maybe Int) -> IO ()
-- printIt (Strict (Just i)) = print i
-- printIt (Strict Nothing)  = putStrLn "Nothing there"
-- @
--
-- Make a @Strict a@ using the @Strict@ constructor if you are
-- constructing it from its individual fields (otherwise it is more
-- efficient to use 'unstrict').
--
-- @
-- makeStrict :: Int -> Strict (Int, String)
-- makeStrict i = Strict (i + 1, show i)
-- @
pattern Strict :: Strictly a => a -> Strict a
pattern Strict x <- (matchStrict->x)
  where Strict = constructStrict

{-# COMPLETE Strict :: Strict #-}
