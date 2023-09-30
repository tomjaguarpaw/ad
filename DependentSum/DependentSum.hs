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
import Data.Proxy (Proxy (Proxy))
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

type FooF :: T -> Type
type family FooF t :: Type where
  FooF A = FooA
  FooF B = FooB

newtype Foo t = Foo {getFoo :: FooF t}

newtype Wrapper t = Wrapper {getFooWrapper :: FooF t}

deriving newtype instance (Show (FooF t)) => Show (Wrapper t)

deriving newtype instance (Read (FooF t)) => Read (Wrapper t)

deriving stock instance (Eq (FooF t)) => Eq (Wrapper t)

deriving stock instance (Ord (FooF t)) => Ord (Wrapper t)

deriving via Knownly (Wrapper t) instance (Known t) => Show (Foo t)

deriving via Knownly (Wrapper t) instance (Known t) => Read (Foo t)

deriving via Knownly (Wrapper t) instance (Known t) => Eq (Foo t)

deriving via Knownly (Wrapper t) instance (Known t) => Ord (Foo t)

-- Lots of boilerplate

eqT ::
  forall (t :: Type) (i :: t) (i' :: t).
  (Index t, Known i, Known i') =>
  Maybe (i :~: i')
eqT = eqT' Proxy Proxy

withKnown ::
  forall (t :: Type) (i :: t) c f r.
  (Known i, Index t, Forall t c f) =>
  ((c (f i)) => r) ->
  r
withKnown = withKnown' @t (Proxy @i) (Proxy @c) (Proxy @f)

coerceMethod ::
  forall (t :: Type) (i :: t) (c :: Type -> Constraint) f a2 a3.
  (Coercible a2 a3, Index t, Forall t c f) =>
  (Known i) =>
  ((c (f i)) => a2) ->
  a3
coerceMethod a2 = coerce @a2 @a3 (withKnown @t @i @c @f a2)

type Known :: forall t. t -> Constraint
class Known (i :: t) where
  know :: Singleton t i

data Dict c where Dict :: (c) => Dict c

type Index :: Type -> Constraint
class Index t where
  data Singleton t :: t -> Type

  type Forall t (c :: Type -> Constraint) (f :: t -> Type) :: Constraint

  eqT' ::
    forall (i :: t) (i' :: t).
    (Known i, Known i') =>
    Proxy i ->
    Proxy i' ->
    Maybe (i :~: i')

  toVal :: Singleton t i -> t

  -- The existence of this method confirms that `instance Known (i ::
  -- t)` has been implemented for all i.
  knowns :: Singleton t i -> Dict (Known i)

  -- Not sure why this requires Proxy arguments
  withKnown' ::
    Proxy i ->
    Proxy c ->
    Proxy f ->
    (Known i, Forall t c f) =>
    ((c (f i)) => r) ->
    r

  applyAny' ::
    Proxy i ->
    (forall (i' :: t). (Known i') => Proxy i' -> r) ->
    t ->
    r

instance Index T where
  data Singleton T t where
    SA :: Singleton T A
    SB :: Singleton T B

  type Forall T c f = (c (f A), c (f B))

  eqT' (Proxy :: Proxy i) (Proxy :: Proxy i')
    | SA <- know @_ @i,
      SA <- know @_ @i' =
        Just Refl
    | SB <- know @_ @i,
      SB <- know @_ @i' =
        Just Refl
    | otherwise =
        Nothing

  toVal = \case
    SA -> A
    SB -> B

  withKnown' =
    \(Proxy :: Proxy i)
     (Proxy :: Proxy c)
     (Proxy :: Proxy f)
     r -> case know @_ @i of
        SA -> r
        SB -> r

  applyAny' (Proxy :: i) r = \case
    A -> r @A Proxy
    B -> r @B Proxy

  knowns = \case
    SA -> Dict
    SB -> Dict

instance Known A where
  know = SA

instance Known B where
  know = SB

newtype Knownly a = Knownly a

instance (Known i, Forall t Show k, Index t) => Show (Knownly (k i)) where
  show = coerceMethod @t @i @Show @k (show @(k i))

instance (Known i, Forall t Read k, Index t) => Read (Knownly (k i)) where
  readPrec = coerceMethod @t @i @Read @k (readPrec @(k i))

instance (Known i, Forall t Eq k, Index t) => Eq (Knownly (k i)) where
  (==) = coerceMethod @t @i @Eq @k ((==) @(k i))

instance (Known i, Forall t Ord k, Index t, Eq (Knownly (k i))) => Ord (Knownly (k i)) where
  compare = coerceMethod @t @i @Ord @k (compare @(k i))

data Some k where
  Some :: (Known t) => k t -> Some k

type SomeT = Some

instance
  forall (t :: Type) (k :: t -> Type).
  (Show t, Index t, forall (i :: t). (Known i) => Show (k i)) =>
  Show (SomeT k)
  where
  show (Some (v :: k i)) = show (toVal (know @_ @i), v)

instance
  forall (t :: Type) (k :: t -> Type).
  (forall i. (Known i) => Eq (k i), Index t) =>
  Eq (SomeT k)
  where
  Some (v1 :: k t1) == Some (v2 :: k t2) = case eqT @_ @t1 @t2 of
    Just Refl -> v1 == v2
    Nothing -> False

readSomeTPayload ::
  forall t i (k :: t -> Type).
  (Read (k i), Known i) =>
  ReadPrec (SomeT k)
readSomeTPayload = Some @i <$> readPrec

applyAny ::
  forall t (i :: t) r.
  (Index t) =>
  (forall (i' :: t). (Known i') => Proxy i' -> r) ->
  t ->
  r
applyAny = applyAny' Proxy

instance
  forall (t :: Type) (k :: t -> Type).
  (forall i. (Known i) => Read (k i), Read t, Index t) =>
  Read (SomeT k)
  where
  readPrec = wrap_tup $ do
    x <- readPrec
    read_comma
    applyAny (\(Proxy :: Proxy i) -> readSomeTPayload @_ @i) x

-- Example to show that it works

mkSomeFoo :: forall t. (Known t) => FooF t -> SomeT Foo
mkSomeFoo = Some @t . Foo

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
