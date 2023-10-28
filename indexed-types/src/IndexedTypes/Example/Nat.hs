{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

-- | This example shows how to define an infinite index type ('Nat')
-- and a type index on that index type ('Foo').
module IndexedTypes.Example.Nat
  ( -- * The type index, @Nat@
    Nat (..),

    -- * Defining @Foo@, a type indexed on @Nat@

    -- | Definition of type that depends on the index @Nat@
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
  ( AsKind (AsType),
    Dict (Dict),
    Index (..),
    Matchable (constructor'),
    asType,
    constructor,
  )
import IndexedTypes.Knownly (Matchably' (Matchably'))
import IndexedTypes.Some (Some (Some))
import Text.Read

-- Index definiton

-- | To make @Nat@ an index type we have to define an 'Index' instance
-- for it, and 'Matchable' instances for all of its values.
data Nat = Z | S Nat deriving (Eq, Show, Read)

-- The most lightweight way is to go via a type family, but that's
-- still quite heavyweight!

-- | The type family that maps each index (i.e. value of type 'Nat')
-- to the payload for that index.
type FooF :: Nat -> Type
type family FooF i :: Type where
  FooF Z = ()
  FooF (S n) = (Int, FooF n)

-- | Finally we define @Foo@, the indexed type itself.
newtype Foo i = Foo (FooF i)
  deriving (Generic)

class (c (FooF i)) => CFooF c i

instance (c (FooF i)) => CFooF c i

deriving via
  Matchably' (CFooF Show) (Foo i)
  instance
    (Matchable i) => Show (Foo i)

deriving via
  Matchably' (CFooF Read) (Foo i)
  instance
    (Matchable i) => Read (Foo i)

deriving via
  Matchably' (CFooF Eq) (Foo i)
  instance
    (Matchable i) => Eq (Foo i)

deriving via
  Matchably' (CFooF Ord) (Foo i)
  instance
    (Matchable i) => Ord (Foo i)

mkSomeFoo :: forall i. (Matchable i) => FooF i -> Some Foo
mkSomeFoo = Some @i . Foo

testCases :: [Some Foo]
testCases =
  [ mkSomeFoo @Z (),
    mkSomeFoo @(S Z) (1, ()),
    mkSomeFoo @(S (S Z)) (1, (2, ()))
  ]

roundtrip :: (Read a, Show a) => a -> Maybe a
roundtrip = readMaybe . show

-- | Example to show that @Show@ and @Read@ instances of @Some@ work.
--
-- @
-- (Z,Foo ())
-- Round-tripped successfully
-- (S Z,Foo (1,()))
-- Round-tripped successfully
-- (S (S Z),Foo (1,(2,())))
-- Round-tripped successfully
-- @
example :: IO ()
example = flip mapM_ testCases $ \some -> do
  print some
  let mr = roundtrip some
  putStrLn $ case mr of
    Just r
      | r == some -> "Round-tripped successfully"
    _ -> "ROUND-TRIP FAILURE!"

-- Lots of boilerplate.  This is all derivable, in principle.

class (forall n. (c n) => c (S n)) => ForallNat c

instance (forall n. (c n) => c (S n)) => ForallNat c

instance Index Nat where
  data Constructor i where
    SZ :: Constructor Z
    SS :: (Matchable n) => Proxy n -> Constructor (S n)

  -- FIXME: Why can't I put (c Z) in ForallNat?
  type Forall Nat c = (c Z, ForallNat c)

  eqT' (Proxy :: Proxy i) (Proxy :: Proxy i')
    | SZ <- constructor @i,
      SZ <- constructor @i' =
        Just Dict
    | SS im1 <- constructor @i,
      SS im1' <- constructor @i',
      Just Dict <- eqT' im1 im1' =
        Just Dict
    | otherwise =
        Nothing

  constructorToValue = \case
    SZ -> Z
    SS (Proxy :: Proxy n) -> S (constructorToValue (constructor @n))

  matchableInAll' =
    \(Proxy :: Proxy i) ->
      case constructor @i of
        SZ -> Dict
        SS im1 -> case matchableInAll' im1 of Dict -> Dict

  toType = \case
    Z -> asType @Z
    S n -> case toType n of AsType (_ :: Proxy n) -> asType @(S n)

instance Matchable Z where
  constructor' = SZ

instance (Matchable n) => Matchable (S n) where
  constructor' = SS Proxy
