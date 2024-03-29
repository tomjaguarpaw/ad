{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

module IndexedTypes.Some (Some (Some), ForallMatchable) where

import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy)
import GHC.Read (expectP, paren)
import IndexedTypes.Index
  ( AsKind (AsType),
    Dict (Dict),
    Index (toType),
    Matchable,
    eqT,
    toValue,
  )
import Text.Read
  ( Lexeme (Punc),
    Read (readPrec),
    ReadPrec,
    parens,
  )

-- | Sometimes known as a "sigma" type, a dependent sum or a dependent
-- pair.
data Some k where
  Some :: (Matchable t) => k t -> Some k

type ForallMatchable ::
  forall (t :: Type).
  (Type -> Constraint) ->
  (t -> Type) ->
  Constraint
class (c t, forall (i :: t). (Matchable i) => c (k i), Index t) => ForallMatchable c (k :: t -> Type)

instance (c t, forall (i :: t). (Matchable i) => c (k i), Index t) => ForallMatchable c k

instance
  forall (t :: Type) (k :: t -> Type).
  (ForallMatchable Show k) =>
  Show (Some k)
  where
  -- In later GHCs this is
  --
  --   show (Some @i v) = ...
  show (Some (v :: k i)) = show (toValue @i, v)

instance
  forall (t :: Type) (k :: t -> Type).
  (ForallMatchable Eq k) =>
  Eq (Some k)
  where
  -- In later GHCs this is
  --
  --   Some @i1 v1 == Some @i2 v2 = ...
  Some (v1 :: k i1) == Some (v2 :: k i2) = case eqT @i1 @i2 of
    Just Dict -> v1 == v2
    Nothing -> False

instance
  forall (t :: Type) (k :: t -> Type).
  (ForallMatchable Read k) =>
  Read (Some k)
  where
  -- Copied from read_tup2
  readPrec = wrap_tup $ do
    AsType (_ :: Proxy i) <- toType <$> readPrec
    read_comma
    Some @i <$> readPrec

-- These ReadPrec combinators are borrowed from
--
-- https://hackage.haskell.org/package/base-4.18.1.0/docs/src/GHC.Read.html#line-681
wrap_tup :: ReadPrec a -> ReadPrec a
wrap_tup p = parens (paren p)

read_comma :: ReadPrec ()
read_comma = expectP (Punc ",")
