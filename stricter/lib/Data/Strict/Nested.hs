{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}

module Data.Strict.Nested
  (
  -- * Introduction

  -- ** Summary

  -- | @strict-nested@ is a library that helps you avoid space leaks,
  -- specifically <http://blog.ezyang.com/2011/05/space-leak-zoo/ thunk leaks>.
  -- It defines a newtype*
  --
  -- @newtype t'Strict' t = v'Strict' t@
  --
  -- with the special property that the @t@ inside the @Strict@ has
  -- been made strict, in the sense that when it is evaluated its
  -- immediate children are evaluated too.  If, for your uses of @t@,
  -- having unevaluated thunks inside it is an invalid state then
  -- wrapping it in @Strict@ "makes invalid states unrepresentable".
  --
  -- \* Actually it's not a newtype but if you think of it as a one
  -- then you'll understand immediately how to use it.  To find out
  -- what it really is, read on.

  -- ** The problem

  -- *** Lazy and strict data

  -- | One circumstance in which thunk leaks occur is when a lazy
  -- field of a data type remains unevaluated for longer than
  -- expected.  By way of example consider the following data type:
  --
  -- @
  -- data Foo = Foo Int Bool
  -- @
  --
  -- During execution of a program what possible states can a value of
  -- type @Foo@ be in?  There are broadly four:
  --
  -- 1. @\<thunk\>@ @ @
  -- 2. @Foo@ @\<evaluated Int\>@ @\<evaluated Bool\>@
  -- 3. @Foo@ @\<evaluated Int\>@ @\<thunk\>@
  -- 4. @Foo@ @\<thunk\>@ @\<evaluated Bool\>@
  --
  -- The @\<thunk\>@s there can be arbitrarily large run time data
  -- structures! Their unexpected occurrence can cause thunk leaks.
  -- What can we do about that?  When programming in a strongly typed
  -- language we aim to "make invalid states unrepresentable" so when
  -- we define a data type like @Foo@ we should consider which are its
  -- valid states.  Haskell is a lazy language so we cannot forbid
  -- state 1*, but are states like 3 and 4 valid?  Perhaps.  We should
  -- carefully consider our use case; but if not (and it's more likely
  -- not than so) then we should forbid those states statically.  How
  -- can we do so?  We can add strictness annotations thus:
  --
  -- @
  -- data FooStrict = FooStrict !Int !Bool
  -- @
  --
  -- (or by enabling @StrictData@ which brutally applies the same
  -- transformation to /every/ data type definition, or @Strict@ which
  -- is even more brutal). @FooStrict@ has only two possible states:
  --
  -- 1. @\<thunk\>@ @ @
  -- 2. @Foo@ @\<evaluated Int\>@ @\<evaluated Bool\>@
  --
  -- Much better!
  --
  -- \* barring unlifted data types, which are out of scope for this
  -- discussion and this library.

  -- *** Nested strict data

  -- | But the above technique is not particularly general.  Consider
  --
  -- @
  -- data Bar = Bar !(Int, Bool) !(Maybe Double)
  -- @
  --
  -- Despite the strictness annotations this type has many
  -- possible states:
  --
  -- 1. @\<thunk\>@ @ @
  --
  -- 2. @Bar (\<thunk\>, \<thunk\>) Nothing@ @ @
  -- 3. @Bar (\<evaulated Int\>, \<thunk\>) Nothing@ @ @
  -- 4. @Bar (\<thunk\>, \<evaluated Bool\>) Nothing@ @ @
  -- 5. @Bar (\<evaluated Int\>, \<evaluated Bool\>) Nothing@ @ @
  --
  -- 6. @Bar (\<thunk\>, \<thunk\>) (Just \<thunk\>)@ @ @
  -- 7. @Bar (\<evaluated Int\>, \<thunk\>) (Just \<thunk\>)@ @ @
  -- 8. @Bar (\<thunk\>, \<evaluated Bool\>) (Just \<thunk\>)@ @ @
  -- 9. @Bar (\<evaluated Int\>, \<evaluated Bool\>) (Just \<thunk\>)@ @ @
  --
  -- 10. @Bar (\<thunk\>, \<thunk\>) (Just \<evaluated Double\>)@ @ @
  -- 11. @Bar (\<evaluated Int\>, \<thunk\>) (Just \<evaluated Double\>)@ @ @
  -- 12. @Bar (\<thunk\>, \<evaluated Bool\>) (Just \<evaluated Double\>)@ @ @
  -- 13. @Bar (\<evaluated Int\>, \<evaluated Bool\>) (Just \<evaluated Double\>)@ @ @
  --
  -- Plenty of thunks for leaks to hide in!  Perhaps for some use
  -- cases all the above states are valid but in most cases it is
  -- overwhelmingly likely that only the following states are valid:
  --
  -- 1. @\<thunk\>@ (because we can't do anything about it anyway)
  -- 2. @Bar (\<evaluated Int\>, \<evaluated Bool\>) Nothing@ @ @
  -- 3. @Bar (\<evaluated Int\>, \<evaluated Bool\>) (Just \<evaluated Double\>)@ @ @
  --
  -- No clever application of strictness annotations can restrict us
  -- to this set of states!  The problem is that there's no way of
  -- "applying strictness inside" the nested data types.

  -- ** The solution

  -- | @strict-nested@ allows you to "apply strictness inside" nested
  -- data types.  For example, if we rewrite @Bar@ as
  --
  --
  -- #barstrict#
  --
  -- @
  -- data BarStrict = BarStrict !(Strict (Int, Bool)) !(Strict (Maybe Double))
  -- @
  --
  -- then only the valid states are representable:
  --
  -- 1. @\<thunk\>@ @ @
  -- 2. @BarStrict (Strict (\<evaluated Int\>, \<evaluated Bool\>)) (Strict Nothing)@ @ @
  -- 3. @BarStrict (Strict (\<evaluated Int\>, \<evaluated Bool\>)) (Strict (Just \<evaluated Double\>))@ @ @
  --
  -- Deeper nesting works too, for example:
  --
  -- #baz#
  --
  -- @
  -- data Baz = Baz !(Strict (Int, Strict (Either Bool Int))) !(Strict (Maybe Double))
  -- @

  -- ** The API

  -- | To understand how to use @strict-nested@ you should imagine
  -- that there is a newtype definition
  --
  -- @
  -- newtype t'Strict' t = v'Strict' t
  -- @
  --
  -- with the special property that the @t@ inside the @Strict@ has
  -- been made strict, in the sense that when it is evaluated its
  -- immediate children are evaluated too (see [The
  -- mechanism](#themechanism) below for details on how this is
  -- achieved).  The data definitions for [@BarStrict@](#barstrict)
  -- and [@Baz@](#baz) above show how to use the t'Strict' type
  -- constructor*.  The examples below show how to use the v'Strict'
  -- data constructor and pattern**.
  --
  -- @
  -- usePattern :: BarStrict -> IO ()
  -- usePattern (BarStrict (Strict (i, b)) (Strict Nothing)) =
  --   putStrLn (show i ++ ": " ++ show b)
  -- usePattern (BarStrict (Strict (i, b)) (Strict (Just d))) =
  --   putStrLn (show i ++ ": " ++ show b ++ " (" ++ show d ++ ")")
  --
  -- useConstructor :: Int -> Bar
  -- useConstructor i = Bar (Strict (i, b)) (Strict m)
  --   where b = isEven i
  --         m = if i \`rem\` 3 == 0 then Nothing else fromIntegral i / 3
  -- @
  --
  -- \* actually a data family
  -- \** actually a bidirectional pattern synonym

  -- | #themechanism#

  -- ** The mechanism

  -- | t'Strict' is a data family that maps each type @t@ to a type
  -- @Strict t@ that is isomorphic to @t@, except that when it is
  -- evaluated all its direct children are evaluated too.  For example
  --
  -- @
  -- data instance Strict (a, b) = StrictPair !a !b
  -- data instance Strict (Maybe a) = StrictNothing | StrictJust !a
  -- @
  --
  -- The v'Strict' bidirectional pattern synonym is just a
  -- mutually-inverse* pair of functions @t -> Strict t@ and @Strict t
  -- -> t@.
  --
  -- \* modulo strictness

  -- *** Efficiency considerations

  -- | Using @strict-nested@ should be zero-cost relative to inserting
  -- 'seq' or bang patterns manually.  In some cases matching the
  -- baseline cost will require using the functions 'strict' and
  -- 'unstrict'.  They provide the same functionality as the v'Strict'
  -- pattern/constructor synonym but can be more efficient in
  -- particular circumstances. We suggest just using v'Strict' until
  -- and unless you find a performance problem.

  -- ** The alternatives

  -- *** @seq@/bang patterns

  -- | It is always possible to use 'seq' (or equivalently bang
  -- patterns) to ensure that invalid thunk states don't arise.  After
  -- all, strictness annotations and strict data types are implemented
  -- merely by automatic insertion of the former!  However, in pratice
  -- it is extremely difficult to maintain the level of discipline
  -- required to make sure all the 'seq' calls or bang patterns are
  -- inserted in the correct places (and not in the incorrect places).
  -- The benefit of programming in a strongly typed functional
  -- language is that we can make invalid states unrepresentable.
  -- That principle applies as much to data type strictness as to any
  -- other use case.

  -- *** deepseq

  -- | <https://hackage.haskell.org/package/deepseq-1.4.5.0/docs/Control-DeepSeq.html deepseq>
  -- is an extremely expensive and blunt hammer.  It has to
  -- walk your entire data structure evaluating any thunks it
  -- encounters.  Were those thunks actually part of a valid state of
  -- your program?  In many (perhaps most) cases they were not!  In those
  -- cases would it not be better to design those thunks out of your data
  -- structures and avoid deepseq entirely?

  -- *** strict

  -- | <https://hackage.haskell.org/package/strict strict> provides a
  -- grab-bag of features related to strictness: strict versions of
  -- basic types, strict I/O, and a class to map between strict and
  -- lazy types (including @ByteString@ and @Text@ types and monad
  -- transformer types).
  --
  -- @strict-nested@ is a much smaller and more coherent subset of the
  -- features of @strict@: it only provides strict versions of basic
  -- types and a class to map between them.  In return for being more
  -- restrictive the mapping can be made almost zero-cost (see
  -- 'strict' and 'unstrict').  Furthermore the v'Strict'
  -- pattern\/constructor is more ergonomic than @toStrict@/@toLazy@
  -- mapping functions.

  -- *** nothunks

  -- |
  -- <https://hackage.haskell.org/package/nothunks-0.1.3/docs/NoThunks-Class.html nothunks>
  -- is a debugging tool that allows inspecting a value at run time to
  -- see if it contains any thunks.  That is, it can check at run time
  -- whether a value is invalid.  But if you can make the invalid
  -- states /unrepresentable/ then why not do so?

  -- * Strict constructor and pattern

  -- | The @Strict@ constructor and pattern are the easiest way to get
  -- started with @strict-nested@.
  pattern Strict
  -- * Accessor functions

  -- | The accessor functions can be more efficient than the v'Strict'
  -- constructor and pattern in some circumstances but we don't
  -- recommend that you use them unless you are experiencing
  -- performance problems.

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
  , NestedStrict
  , NotYetImplemented
  ) where

import Unsafe.Coerce (unsafeCoerce)
import GHC.TypeLits
import Data.Kind (Constraint)

-- | A type can be given a @Strictly@ instance when it has a very
-- cheap conversion to and from a strict type, @Strict a@.
class Strictly t where
  -- | Isomorphic to the type @a@, except that when it is evaulated its
  -- immediate children are evaluated too.
  data Strict t
  -- | Make a @Strict a@ using 'strict' if you obtained an @a@ from
  -- elsewhere (otherwise, if you have the components of @a@
  -- separately, then it is more efficient to use the v'Strict'
  -- constructor instead).
  --
  -- @
  -- makeStrict :: (Int, Strict (Int, String)) -> Int
  -- makeStrict (i, s) = i + f (strict s)
  -- @
  strict :: t -> Strict t
  -- | Access the contents of a @Strict a@, but not its fields, using
  -- @unstrict@ (if you want access to the fields then it is more
  -- efficient to use the v'Strict' pattern).
  --
  -- @
  -- strictMaybe :: r -> (a -> r) -> Strict (Maybe a) -> r
  -- strictMaybe r f sm = maybe r f (unstrict sm)
  -- @
  unstrict :: Strict t -> t
  -- | Used to implement the v'Strict' pattern synonym.  You should
  -- never need to use @matchStrict@ unless you are defining your own
  -- instance of @Strictly@.
  matchStrict :: Strict t -> t
  -- | Used to implement the v'Strict' constructor.  You should never
  -- need to use @constructStrict@ unless you are defining your own
  -- instance of @Strictly@.
  constructStrict :: t -> Strict t

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
-- strict as they can be.  There is no need to wrap them in t'Strict'!
type family AlreadyStrict t :: Constraint
type instance AlreadyStrict t =
  TypeError (('ShowType t ':<>: 'Text " is already strict.")
              ':$$: ('Text "Just use "
                     ':<>: 'ShowType t
                     ':<>: 'Text " rather than Strict ("
                     ':<>: 'ShowType t
                     ':<>: 'Text ")"))

-- | Some data types, such as @[a]@, can't be made strict in a
-- zero-cost way.
type family Can'tBeStrict t :: Constraint
type instance Can'tBeStrict t =
  TypeError ('ShowType t ':<>: 'Text " can't be made strict.")

-- | Some 'Strictly' instances are not yet implemented.  Please file
-- an issue if you need them.
type family NotYetImplemented t :: Constraint
type instance NotYetImplemented t =
  TypeError ('Text "Strict is not yet implemented for " ':<>: 'ShowType t
             ':$$: 'Text "Please file an issue if you need it")

-- | It is redundant to nest t'Strict', e.g. @Strict (Strict (a, b))@.
-- Just use one layer of t'Strict'.
type family NestedStrict t :: Constraint
type instance NestedStrict t =
  TypeError ('Text "It is redundant to nest Strict"
             ':$$: 'Text "In type Strict (Strict (" ':<>: 'ShowType t ':<>: 'Text "))"
             ':$$: 'Text "Just use Strict (" ':<>: 'ShowType t ':<>: 'Text ") instead")

instance AlreadyStrict () => Strictly ()
instance AlreadyStrict Bool => Strictly Bool
instance AlreadyStrict Int => Strictly Int
instance AlreadyStrict Integer => Strictly Integer
instance AlreadyStrict Float => Strictly Float
instance AlreadyStrict Word => Strictly Word
instance AlreadyStrict Double => Strictly Double
instance AlreadyStrict Ordering => Strictly Ordering
instance AlreadyStrict Char => Strictly Char

instance Can'tBeStrict [t] => Strictly [t]
instance Can'tBeStrict (IO a) => Strictly (IO a)

instance NotYetImplemented (x1, x2, x3) => Strictly (x1, x2, x3)
instance NotYetImplemented (x1, x2, x3, x4) => Strictly (x1, x2, x3, x4)
instance NotYetImplemented (x1, x2, x3, x4, x5) => Strictly (x1, x2, x3, x4, x5)
instance NotYetImplemented (x1, x2, x3, x4, x5, x6) => Strictly (x1, x2, x3, x4, x5, x6)

instance NestedStrict t => Strictly (Strict t)

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
pattern Strict :: Strictly t => t -> Strict t
pattern Strict x <- (matchStrict->x)
  where Strict = constructStrict

{-# COMPLETE Strict :: Strict #-}
