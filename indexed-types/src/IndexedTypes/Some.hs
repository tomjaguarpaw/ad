{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

module IndexedTypes.Some (Some (Some)) where

import Data.Kind (Type)
import Data.Proxy (Proxy (Proxy))
import GHC.Read (expectP, paren)
import IndexedTypes.Index
  ( Index (toType),
    Known,
    TypeOfKind (TypeIs),
    eqT,
    toValue,
  )
import Text.Read
  ( Lexeme (Punc),
    Read (readPrec),
    ReadPrec,
    parens,
  )
import Type.Reflection ((:~:) (Refl))

-- | Sometimes known as a "sigma" type.
data Some k where
  Some :: (Known t) => k t -> Some k

instance
  forall (t :: Type) (k :: t -> Type).
  (Show t, forall (i :: t). (Known i) => Show (k i), Index t) =>
  Show (Some k)
  where
  -- In later GHCs this is
  --
  --   show (Some @i v) = ...
  show (Some (v :: k i)) = show (toValue @_ @i, v)

instance
  forall (t :: Type) (k :: t -> Type).
  (forall i. (Known i) => Eq (k i), Index t) =>
  Eq (Some k)
  where
  -- In later GHCs this is
  --
  --   Some @i1 v1 == Some @i2 v2 = ...
  Some (v1 :: k i1) == Some (v2 :: k i2) = case eqT @_ @i1 @i2 of
    Just Refl -> v1 == v2
    Nothing -> False

instance
  forall (t :: Type) (k :: t -> Type).
  (Read t, forall i. (Known i) => Read (k i), Index t) =>
  Read (Some k)
  where
  -- Copied from read_tup2
  readPrec = wrap_tup $ do
    i <- readPrec
    read_comma
    case toType i of
      TypeIs (Proxy :: Proxy i') -> Some @i' <$> readPrec

-- These ReadPrec combinators are borrowed from
--
-- https://hackage.haskell.org/package/base-4.18.1.0/docs/src/GHC.Read.html#line-681
wrap_tup :: ReadPrec a -> ReadPrec a
wrap_tup p = parens (paren p)

read_comma :: ReadPrec ()
read_comma = expectP (Punc ",")
