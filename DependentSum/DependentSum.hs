{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module DependentSum where

import Data.Kind (Constraint, Type)
import GHC.Read (expectP, paren)
import Text.Read
  ( Lexeme (Punc),
    Read (readPrec),
    ReadPrec,
    parens,
    readMaybe,
  )

-- Index definiton

data T = A | B deriving (Show, Read)

-- Definition of type that depends on index.  The most lightweight way
-- is to go via a type family, but that's still quite heavyweight!

data FooA = FooA1 Int | FooA2 Bool
  deriving (Read, Show)

data FooB = FooB1 Char | FooB2 String
  deriving (Read, Show)

type FooF :: T -> Type
type family FooF a where
  FooF A = FooA
  FooF B = FooB

newtype Foo t = Foo {getFoo :: FooF t}

-- Lots of boilerplate

data ST :: T -> Type where
  SA :: ST A
  SB :: ST B

stTot :: ST t -> T
stTot = \case
  SA -> A
  SB -> B

class KnownT a where
  knownT :: ST a

instance KnownT A where
  knownT = SA

instance KnownT B where
  knownT = SB

type ForallFooF :: (Type -> Constraint) -> Constraint
type ForallFooF c = (c (FooF A), c (FooF B))

withKnownT ::
  forall t c r.
  (KnownT t, ForallFooF c) =>
  ((c (FooF t)) => r) ->
  r
withKnownT r = case knownT @t of
  SA -> r
  SB -> r

instance (KnownT t, ForallFooF Show) => Show (Foo t) where
  show (Foo v) = withKnownT @t @Show show v

instance (KnownT t, ForallFooF Read) => Read (Foo t) where
  readPrec = Foo <$> withKnownT @t @Read readPrec

data SomeT k where
  SomeT :: (KnownT t) => k t -> SomeT k

mkSomeFoo :: forall t. (KnownT t) => FooF t -> SomeT Foo
mkSomeFoo = SomeT @t . Foo

instance (forall t. (KnownT t) => Show (k t)) => Show (SomeT k) where
  show (SomeT (v :: k t)) = show (stTot (knownT @t), v)

readSomeTPayload :: forall i k. (Read (k i), KnownT i) => ReadPrec (SomeT k)
readSomeTPayload = SomeT @i <$> readPrec

instance (forall t. (KnownT t) => Read (k t)) => Read (SomeT k) where
  readPrec = wrap_tup $ do
    x <- readPrec
    read_comma
    case x of
      A -> readSomeTPayload @A
      B -> readSomeTPayload @B

-- Example to show that it works

testCases =
  [ mkSomeFoo @A (FooA1 1),
    mkSomeFoo @A (FooA2 True),
    mkSomeFoo @B (FooB1 'x'),
    mkSomeFoo @B (FooB2 "hello")
  ]

roundtrip :: (Read a, Show a) => a -> Maybe a
roundtrip = readMaybe . show

example :: IO ()
example = flip mapM_ testCases $ \someT -> do
  print someT
  let mr = roundtrip someT
  case mr of
    Just r -> print r
    Nothing -> putStrLn "No read"

-- These ReadPrec combinators are borrowed from
--
-- https://hackage.haskell.org/package/base-4.18.1.0/docs/src/GHC.Read.html#line-681

wrap_tup :: ReadPrec a -> ReadPrec a
wrap_tup p = parens (paren p)

read_tup2 :: (Read a, Read b) => ReadPrec (a, b)
-- Reads "a , b"  no parens!
read_tup2 = do
  x <- readPrec
  read_comma
  y <- readPrec
  return (x, y)

read_comma :: ReadPrec ()
read_comma = expectP (Punc ",")
