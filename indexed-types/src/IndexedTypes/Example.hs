{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

-- | This example shows how to define an index type ('T') and a type
-- index on that index type ('Foo').
module IndexedTypes.Example
  ( -- * The type index
    T (..),

    -- * Defining @Foo@, a type indexed on @T@

    -- | Definition of type that depends on the index 'T'.
    FooA (..),
    FooBC (..),
    FooF,
    Foo (..),

    -- * Deriving instances for @Foo@
    FooWrapper (..),

    -- * Example
    example,
  )
where

import Data.Kind (Type)
import Data.Proxy (Proxy (Proxy))
import IndexedTypes.Index
  ( AsKind (AsType),
    Contains (Contains),
    Index (..),
    Known (know'),
    know,
  )
import IndexedTypes.Knownly (Knownly (Knownly))
import IndexedTypes.Some (Some (Some))
import Text.Read (readMaybe)
import Type.Reflection ((:~:) (Refl))

-- Index definiton

-- | To make @T@ an index type we have to define an 'Index' instance
-- for it, and 'Known' instances for all of its values ('A', 'B' and
-- 'C').
data T = A | B | C deriving (Eq, Show, Read)

-- The most lightweight way is to go via a type family, but that's
-- still quite heavyweight!

-- | The payload for when the index is 'A'
data FooA = FooA1 Int | FooA2 Bool
  deriving (Eq, Ord, Read, Show)

-- | The payload for when the index is 'B' or 'C'. (We're choosing the
-- payload of @B@ and @C@ to be the same here, just to demonstrate
-- that that /can/ be done.)
data FooBC = FooBC1 Char | FooBC2 String
  deriving (Eq, Ord, Read, Show)

-- | The type family that maps each index (i.e. value of type 'T') to
-- the payload for that index.
type FooF :: T -> Type
type family FooF i :: Type where
  FooF A = FooA
  FooF B = FooBC
  FooF C = FooBC

-- | Finally we define @Foo@, the indexed type itself.
newtype Foo i = Foo (FooF i)

-- | A wrapper type, with the same contents as @Foo@, purely for the
-- purpose of deriving instances.
--
-- The instances we derive for @FooWrapper@ are only used by the
-- @deriving via@ clauses which derive instances for @Foo@.  If you
-- were defining an indexed type like @Foo@ in your own code you
-- wouldn't export the equivalent of @FooWrapper@.  It wouldn't be
-- needed anywhere else.
--
-- The technical reason that we need to do this is that we want
-- the instance
--
-- * @Known i => Show (Foo i)@
--
-- However, GHC's @deriving@ only allows us to directly derive
--
-- * @Show (FooF A) => Show (Foo A)@
-- * @Show (FooF B) => Show (Foo B)@
-- * @Show (FooF C) => Show (Foo C)@
--
-- so instead we derive those instances for the @newtype@ @FooWrapper@
-- instead, and then use @deriving via@ with 'Knownly', to derive the
-- instances for @Foo@.  'Knownly'\'s purpose is to convert the
-- constraint @(Show (FooF A), Show (FooF B), Show (FooF C))@ into
-- @Known i@.
--
-- If GHC's deriving mechanism were more flexible perhaps we wouldn't
-- have to go all round the houses like this.
newtype FooWrapper i = Wrapper (FooF i)

-- | derived as a @newtype@ instance
deriving newtype instance (Show (FooF i)) => Show (FooWrapper i)

-- | derived as a @newtype@ instance
deriving newtype instance (Read (FooF i)) => Read (FooWrapper i)

-- | derived as a @stock@ instance
deriving stock instance (Eq (FooF i)) => Eq (FooWrapper i)

-- | derived as a @stock@ instance
deriving stock instance (Ord (FooF i)) => Ord (FooWrapper i)

-- | derived via @Knownly (FooWrapper i)@
deriving via Knownly (FooWrapper i) instance (Known i) => Show (Foo i)

-- | derived via @Knownly (FooWrapper i)@
deriving via Knownly (FooWrapper i) instance (Known i) => Read (Foo i)

-- | derived via @Knownly (FooWrapper i)@
deriving via Knownly (FooWrapper i) instance (Known i) => Eq (Foo i)

-- | derived via @Knownly (FooWrapper i)@
deriving via Knownly (FooWrapper i) instance (Known i) => Ord (Foo i)

mkSomeFoo :: forall i. (Known i) => FooF i -> Some Foo
mkSomeFoo = Some @i . Foo

testCases :: [Some Foo]
testCases =
  [ mkSomeFoo @A (FooA1 1),
    mkSomeFoo @A (FooA2 True),
    mkSomeFoo @B (FooBC1 'x'),
    mkSomeFoo @B (FooBC2 "hello"),
    mkSomeFoo @C (FooBC1 'x'),
    mkSomeFoo @C (FooBC2 "hello")
  ]

roundtrip :: (Read a, Show a) => a -> Maybe a
roundtrip = readMaybe . show

-- | Example to show that @Show@ and @Read@ instances of @Some@ work.
--
-- @
-- (A,FooA1 1)
-- Round-tripped successfully
-- (A,FooA2 True)
-- Round-tripped successfully
-- (B,FooBC1 'x')
-- Round-tripped successfully
-- (B,FooBC2 "hello")
-- Round-tripped successfully
-- (C,FooBC1 'x')
-- Round-tripped successfully
-- (C,FooBC2 "hello")
-- Round-tripped successfully
-- @
example :: IO ()
example = flip mapM_ testCases $ \someT -> do
  print someT
  let mr = roundtrip someT
  putStrLn $ case mr of
    Just r
      | r == someT -> "Round-tripped successfully"
    _ -> "ROUND-TRIP FAILURE!"

-- Lots of boilerplate.  This is all derivable, in principle.

instance Index T where
  data Singleton i where
    SA :: Singleton A
    SB :: Singleton B
    SC :: Singleton C

  type All T = [A, B, C]

  eqT' (Proxy :: Proxy i) (Proxy :: Proxy i')
    | SA <- know @i,
      SA <- know @i' =
        Just Refl
    | SB <- know @i,
      SB <- know @i' =
        Just Refl
    | SC <- know @i,
      SC <- know @i' =
        Just Refl
    | otherwise =
        Nothing

  singletonToValue = \case
    SA -> A
    SB -> B
    SC -> C

  knowAll' =
    \(Proxy :: Proxy i) ->
      case know @i of
        SA -> Contains
        SB -> Contains
        SC -> Contains

  toType = \case
    A -> AsType @_ @A Proxy
    B -> AsType @_ @B Proxy
    C -> AsType @_ @C Proxy

instance Known A where
  know' = SA

instance Known B where
  know' = SB

instance Known C where
  know' = SC
