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

module IndexedTypes.Example where

import Data.Kind (Type)
import Data.Proxy (Proxy (Proxy))
import IndexedTypes.Index (Index (..), Known (know))
import IndexedTypes.Knownly (Knownly (Knownly))
import IndexedTypes.Some (Some (Some))
import Text.Read (readMaybe)
import Type.Reflection ((:~:) (Refl))

-- Index definiton

data T = A | B | C deriving (Eq, Ord, Show, Read)

-- Definition of type that depends on index.  The most lightweight way
-- is to go via a type family, but that's still quite heavyweight!

data FooA = FooA1 Int | FooA2 Bool
  deriving (Eq, Ord, Read, Show)

data FooB = FooB1 Char | FooB2 String
  deriving (Eq, Ord, Read, Show)

type FooF :: T -> Type
type family FooF t :: Type where
  FooF A = FooA
  FooF B = FooB
  FooF C = FooB

newtype Foo t = Foo {getFoo :: FooF t}

newtype FooWrapper t = Wrapper {getFooWrapper :: FooF t}

deriving newtype instance (Show (FooF t)) => Show (FooWrapper t)

deriving newtype instance (Read (FooF t)) => Read (FooWrapper t)

deriving stock instance (Eq (FooF t)) => Eq (FooWrapper t)

deriving stock instance (Ord (FooF t)) => Ord (FooWrapper t)

deriving via Knownly (FooWrapper t) instance (Known t) => Show (Foo t)

deriving via Knownly (FooWrapper t) instance (Known t) => Read (Foo t)

deriving via Knownly (FooWrapper t) instance (Known t) => Eq (Foo t)

deriving via Knownly (FooWrapper t) instance (Known t) => Ord (Foo t)

mkSomeFoo :: forall t. (Known t) => FooF t -> Some Foo
mkSomeFoo = Some @t . Foo

testCases :: [Some Foo]
testCases =
  [ mkSomeFoo @A (FooA1 1),
    mkSomeFoo @A (FooA2 True),
    mkSomeFoo @B (FooB1 'x'),
    mkSomeFoo @B (FooB2 "hello"),
    mkSomeFoo @C (FooB1 'x'),
    mkSomeFoo @C (FooB2 "hello")
  ]

roundtrip :: (Read a, Show a) => a -> Maybe a
roundtrip = readMaybe . show

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

  applyAny' (Proxy :: i) r = \case
    A -> r @A Proxy
    B -> r @B Proxy
    C -> r @C Proxy

instance Known A where
  know = SA

instance Known B where
  know = SB

instance Known C where
  know = SC
