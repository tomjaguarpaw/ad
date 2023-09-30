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
  | SA <- know @_ @t,
    SA <- know @_ @t' =
      Just Refl
  | SB <- know @_ @t,
    SB <- know @_ @t' =
      Just Refl
  | otherwise =
      Nothing

withKnown ::
  forall t (i :: t) c f r.
  (Known i, Index t, Forall t f c) =>
  ((c (f i)) => r) ->
  r
withKnown = withKnown' @t (Proxy @i) (Proxy @c) (Proxy @f)

coerceMethod ::
  forall (t :: Type) (i :: t) (c :: Type -> Constraint) f a2 a3.
  (Coercible a2 a3, Index t, Forall t f c) =>
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

  type Forall t (f :: t -> Type) (c :: Type -> Constraint) :: Constraint

  toVal :: Singleton t i -> t

  -- The existence of this method confirms that `instance Known (i ::
  -- t)` has been implemented for all i.
  knowns :: Singleton t i -> Dict (Known i)

  -- Not sure why this requires Proxy arguments
  withKnown' ::
    Proxy i ->
    Proxy c ->
    Proxy f ->
    (Known i, Forall t f c) =>
    ((c (f i)) => r) ->
    r

instance Index T where
  data Singleton T t where
    SA :: Singleton T A
    SB :: Singleton T B

  type Forall T f c = (c (f A), c (f B))

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

  knowns = \case
    SA -> Dict
    SB -> Dict

type KnownT :: T -> Constraint
type KnownT = Known

instance Known A where
  know = SA

instance Known B where
  know = SB

newtype Wrapper k t = Wrapper {getFooWrapper :: FF k t}

deriving newtype instance (Show (FF FooFF t)) => Show (Wrapper FooFF t)

deriving newtype instance (Read (FF FooFF t)) => Read (Wrapper FooFF t)

deriving newtype instance (Eq (FF FooFF t)) => Eq (Wrapper FooFF t)

deriving newtype instance (Ord (FF FooFF t)) => Ord (Wrapper FooFF t)

newtype Wrapper2 a = Worapper2 a

instance (Known t) => Show (Wrapper2 (Wrapper FooFF t)) where
  show = coerceMethod @T @t @Show @(Wrapper FooFF) (show @(Wrapper FooFF t))

instance (Known t) => Read (Wrapper2 (Wrapper FooFF t)) where
  readPrec = coerceMethod @T @t @Read @(Wrapper FooFF) (readPrec @(Wrapper FooFF t))

instance (Known t) => Eq (Wrapper2 (Wrapper FooFF t)) where
  (==) = coerceMethod @T @t @Eq @(Wrapper FooFF) ((==) @(Wrapper FooFF t))

instance (Known t) => Ord (Wrapper2 (Wrapper FooFF t)) where
  compare = coerceMethod @T @t @Ord @(Wrapper FooFF) (compare @(Wrapper FooFF t))

deriving via Wrapper2 (Wrapper FooFF t) instance (Known t) => Show (Foo t)

deriving via Wrapper2 (Wrapper FooFF t) instance (Known t) => Read (Foo t)

deriving via Wrapper2 (Wrapper FooFF t) instance (Known t) => Eq (Foo t)

deriving via Wrapper2 (Wrapper FooFF t) instance (Known t) => Ord (Foo t)

data Some k where
  Some :: (Known t) => k t -> Some k

type SomeT = Some

instance (forall t. (KnownT t) => Show (k t)) => Show (SomeT k) where
  show (Some (v :: k t)) = show (toVal (know @_ @t), v)

instance (forall t. (KnownT t) => Eq (k t)) => Eq (SomeT k) where
  Some (v1 :: k t1) == Some (v2 :: k t2) = case eqT @t1 @t2 of
    Just Refl -> v1 == v2
    Nothing -> False

readSomeTPayload :: forall i k. (Read (k i), KnownT i) => ReadPrec (SomeT k)
readSomeTPayload = Some @i <$> readPrec

instance (forall t. (KnownT t) => Read (k t)) => Read (SomeT k) where
  readPrec = wrap_tup $ do
    x <- readPrec
    read_comma
    case x of
      A -> readSomeTPayload @A
      B -> readSomeTPayload @B

-- Example to show that it works

mkSomeFoo :: forall t. (Known t) => FF FooFF t -> SomeT Foo
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
