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
    Foo (..),

    -- * Deriving instances for @Foo@
    FooWrapper (..),

    -- * Example
    example,
  )
where

import Data.Kind (Type)
import Data.Proxy (Proxy (Proxy))
import IndexedTypes.Index (Index (..), Known (know))
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

type FooF :: T -> Type
type family FooF t :: Type where
  FooF A = FooA
  FooF B = FooBC
  FooF C = FooBC

newtype Foo t = Foo {getFoo :: FooF t}

-- | A wrapper type, with the contents as @Foo@, purely for the purpose
-- of deriving instances.
newtype FooWrapper t = Wrapper {getFooWrapper :: FooF t}

-- | derived as a @newtype@ instance
deriving newtype instance (Show (FooF t)) => Show (FooWrapper t)

-- | derived as a @newtype@ instance
deriving newtype instance (Read (FooF t)) => Read (FooWrapper t)

-- | derived as a @stock@ instance
deriving stock instance (Eq (FooF t)) => Eq (FooWrapper t)

-- | derived as a @stock@ instance
deriving stock instance (Ord (FooF t)) => Ord (FooWrapper t)

-- | derived via @Knownly (FooWrapper t)@
deriving via Knownly (FooWrapper t) instance (Known t) => Show (Foo t)

-- | derived via @Knownly (FooWrapper t)@
deriving via Knownly (FooWrapper t) instance (Known t) => Read (Foo t)

-- | derived via @Knownly (FooWrapper t)@
deriving via Knownly (FooWrapper t) instance (Known t) => Eq (Foo t)

-- | derived via @Knownly (FooWrapper t)@
deriving via Knownly (FooWrapper t) instance (Known t) => Ord (Foo t)

mkSomeFoo :: forall t. (Known t) => FooF t -> Some Foo
mkSomeFoo = Some @t . Foo

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
  data Singleton T t where
    SA :: Singleton T A
    SB :: Singleton T B
    SC :: Singleton T C

  type Forall T c f = (c (f A), c (f B), c (f C))

  eqT' (Proxy :: Proxy i) (Proxy :: Proxy i')
    | SA <- know @_ @i,
      SA <- know @_ @i' =
        Just Refl
    | SB <- know @_ @i,
      SB <- know @_ @i' =
        Just Refl
    | SC <- know @_ @i,
      SC <- know @_ @i' =
        Just Refl
    | otherwise =
        Nothing

  toVal = \case
    SA -> A
    SB -> B
    SC -> C

  withKnown' =
    \(Proxy :: Proxy i)
     (Proxy :: Proxy c)
     (Proxy :: Proxy f)
     r -> case know @_ @i of
        SA -> r
        SB -> r
        SC -> r

  applyAny' (Proxy :: i) i' r = case i' of
    A -> r @A Proxy
    B -> r @B Proxy
    C -> r @C Proxy

instance Known A where
  know = SA

instance Known B where
  know = SB

instance Known C where
  know = SC
