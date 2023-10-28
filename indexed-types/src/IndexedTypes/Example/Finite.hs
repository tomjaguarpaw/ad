{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
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
module IndexedTypes.Example.Finite
  ( -- * The type index
    T (..),

    -- * Defining @Foo@, a type indexed on @T@

    -- | Definition of type that depends on the index 'T'.
    FooA (..),
    FooBC (..),
    FooF,
    Foo (..),

    -- * Example
    example,
  )
where

import Data.Kind (Type)
import Data.Proxy (Proxy (Proxy))
import GHC.Generics (Generic)
import IndexedTypes.Index
  ( Dict (Dict),
    For,
    Index (..),
    Matchable (constructor'),
    asType,
    constructor,
  )
import IndexedTypes.Knownly (Matchably (Matchably))
import IndexedTypes.Some (Some (Some))
import Text.Read (readMaybe)

-- Index definiton

-- | To make @T@ an index type we have to define an 'Index' instance
-- for it, and 'Matchable' instances for all of its values ('A', 'B' and
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
  deriving (Generic)

deriving via Matchably (Foo i) instance (Matchable i) => Show (Foo i)

deriving via Matchably (Foo i) instance (Matchable i) => Read (Foo i)

deriving via Matchably (Foo i) instance (Matchable i) => Ord (Foo i)

deriving via Matchably (Foo i) instance (Matchable i) => Eq (Foo i)

mkSomeFoo :: forall i. (Matchable i) => FooF i -> Some Foo
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
  data Constructor i where
    SA :: Constructor A
    SB :: Constructor B
    SC :: Constructor C

  type Forall T c = For T c [A, B, C]

  eqT' (Proxy :: Proxy i) (Proxy :: Proxy i')
    | SA <- constructor @i,
      SA <- constructor @i' =
        Just Dict
    | SB <- constructor @i,
      SB <- constructor @i' =
        Just Dict
    | SC <- constructor @i,
      SC <- constructor @i' =
        Just Dict
    | otherwise =
        Nothing

  constructorToValue = \case
    SA -> A
    SB -> B
    SC -> C

  matchableInAll' =
    \(Proxy :: Proxy i) ->
      case constructor @i of
        SA -> Dict
        SB -> Dict
        SC -> Dict

  toType = \case
    A -> asType @A
    B -> asType @B
    C -> asType @C

instance Matchable A where
  constructor' = SA

instance Matchable B where
  constructor' = SB

instance Matchable C where
  constructor' = SC
