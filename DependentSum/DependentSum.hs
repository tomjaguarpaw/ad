{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module DependentSum where

import Data.Coerce (Coercible, coerce)
import Data.Kind (Constraint, Type)
import GHC.Read (expectP, paren)
import Text.Read
  ( Lexeme (Punc),
    Read (readPrec),
    ReadPrec,
    parens,
    readMaybe,
  )
import Type.Reflection ((:~:) (Refl))

-- Index definiton

data T = A | B deriving (Show, Read)

-- Definition of type that depends on index.  The most lightweight way
-- is to go via a type family, but that's still quite heavyweight!

data FooA = FooA1 Int | FooA2 Bool
  deriving (Eq, Ord, Read, Show)

data FooB = FooB1 Char | FooB2 String
  deriving (Eq, Ord, Read, Show)

type FF :: forall t. forall (k :: t -> Type) -> t -> Type
type family FF f a

type FooFF :: T -> Type
data FooFF t

type instance FF FooFF A = FooA

type instance FF FooFF B = FooB

newtype Foo t = Foo {getFoo :: FF FooFF t}

-- Lots of boilerplate

eqT :: forall t t'. (KnownT t, KnownT t') => Maybe (t :~: t')
eqT
  | SA <- knownT @t,
    SA <- knownT @t' =
      Just Refl
  | SB <- knownT @t,
    SB <- knownT @t' =
      Just Refl
  | otherwise =
      Nothing

stTot :: ST t -> T
stTot = \case
  SA -> A
  SB -> B

type ForallFooF :: (T -> Type) -> (Type -> Constraint) -> Constraint
type ForallFooF f c = (c (f A), c (f B))

withKnownT ::
  forall t c f r.
  (KnownT t, ForallFooF f c) =>
  ((c (f t)) => r) ->
  r
withKnownT r = case knownT @t of
  SA -> r
  SB -> r

coerceMethod ::
  forall t (c :: Type -> Constraint) f a2 a3.
  (Coercible a2 a3) =>
  (ForallFooF f c) =>
  (KnownT t) =>
  ((c (f t)) => a2) ->
  a3
coerceMethod a2 = coerce @a2 @a3 (withKnownT @t @c @f a2)

type Known :: forall t. t -> Constraint
class Known (i :: t) where
  know :: Singleton t i

type Index :: Type -> Constraint
class Index t where
  data Singleton t :: t -> Type

instance Index T where
  data Singleton T t where
    SA :: Singleton T A
    SB :: Singleton T B

type KnownT :: T -> Constraint
type KnownT = Known

knownT :: forall (t :: T). (Known t) => Singleton T t
knownT = know

instance Known A where
  know = SA

instance Known B where
  know = SB

-- FIXME: Eventually remove this
type ST = Singleton T

newtype FooWrapper t = FooWrapper {getFooWrapper :: FF FooFF t}

deriving newtype instance (Show (FF FooFF t)) => Show (FooWrapper t)

deriving newtype instance (Read (FF FooFF t)) => Read (FooWrapper t)

deriving newtype instance (Eq (FF FooFF t)) => Eq (FooWrapper t)

deriving newtype instance (Ord (FF FooFF t)) => Ord (FooWrapper t)

newtype Wrapper2 f t = Worapper2 (f t)

instance (KnownT t) => Show (Wrapper2 FooWrapper t) where
  show = coerceMethod @t @Show @FooWrapper (show @(FooWrapper t))

instance (KnownT t) => Read (Wrapper2 FooWrapper t) where
  readPrec = coerceMethod @t @Read @FooWrapper (readPrec @(FooWrapper t))

instance (KnownT t) => Eq (Wrapper2 FooWrapper t) where
  (==) = coerceMethod @t @Eq @FooWrapper ((==) @(FooWrapper t))

instance (KnownT t) => Ord (Wrapper2 FooWrapper t) where
  compare = coerceMethod @t @Ord @FooWrapper (compare @(FooWrapper t))

deriving via Wrapper2 FooWrapper t instance (KnownT t) => Show (Foo t)

deriving via Wrapper2 FooWrapper t instance (KnownT t) => Read (Foo t)

deriving via Wrapper2 FooWrapper t instance (KnownT t) => Eq (Foo t)

deriving via Wrapper2 FooWrapper t instance (KnownT t) => Ord (Foo t)

data SomeT k where
  SomeT :: (KnownT t) => k t -> SomeT k

mkSomeFoo :: forall t. (KnownT t) => FF FooFF t -> SomeT Foo
mkSomeFoo = SomeT @t . Foo

instance (forall t. (KnownT t) => Show (k t)) => Show (SomeT k) where
  show (SomeT (v :: k t)) = show (stTot (knownT @t), v)

instance (forall t. (KnownT t) => Eq (k t)) => Eq (SomeT k) where
  SomeT (v1 :: k t1) == SomeT (v2 :: k t2) = case eqT @t1 @t2 of
    Just Refl -> v1 == v2
    Nothing -> False

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

testCases :: [SomeT Foo]
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
  putStrLn $ case mr of
    Just r
      | r == someT -> "Round-tripped successfully"
    _ -> "ROUND-TRIP FAILURE!"

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
