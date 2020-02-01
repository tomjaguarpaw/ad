{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs      #-}
{-# LANGUAGE DataKinds  #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -Wall #-}

module PurePP where

import Data.Copointed
import Data.Functor.Contravariant
import Data.Distributive
import Data.Profunctor

-- A polynomial in a single variable X over ring a
data Poly a =
    Unit
  | X
  | Scale a (Poly a)
  | Product (Poly a) (Poly a)
  | Sum (Poly a) (Poly a)

-- A polynomial in a single variable X over ring a
data PolyExp a =
    UnitE
  | XE
  | ScaleE a (PolyExp a)
  | Exp (PolyExp a) a
  | ProductE (PolyExp a) (PolyExp a)
  | SumE (PolyExp a) (PolyExp a)

-- A polynomial functor (with shape p)
data PolyF p x where
  UnitF    :: PolyF 'Unit x
  XF       :: x -> PolyF 'X x
  ScaleF   :: a -> PolyF p x -> PolyF ('Scale a p) x
  ProductF :: PolyF p x -> PolyF p' x -> PolyF ('Product p p') x
  SumF     :: Either (PolyF p x) (PolyF p' x) -> PolyF ('Sum p p') x

-- A polyexp functor (with shape p)
data PolyEF p x where
  UnitEF    :: PolyEF 'UnitE x
  XEF       :: x -> PolyEF 'XE x
  ScaleEF   :: a -> PolyEF p x -> PolyEF ('ScaleE a p) x
  ProductEF :: PolyEF p x -> PolyEF p' x -> PolyEF ('ProductE p p') x
  SumEF     :: Either (PolyEF p x) (PolyEF p' x) -> PolyEF ('SumE p p') x
  ExpEF     :: (a -> PolyEF p x) -> PolyEF ('Exp p a) x

class Profunctor p => ProfunctorMap (f :: k -> * -> *) p where
  pmap :: p a b -> p (f c a) (f c b)

data Wrapped p f a b = Wrapped { unwrap :: p a (f b) }

instance (Profunctor p, Functor f) => Profunctor (Wrapped p f) where
  dimap g h (Wrapped f) = Wrapped (dimap g (fmap h) f)

data Constrained c f a where
  Constrained :: c f => f a -> Constrained c f a

unConstrained :: c f => Constrained c f a -> f a
unConstrained = \case Constrained g -> g

type LensLike f s t a b = forall p. ProfunctorMap f p => p a b -> p s t

-- Someone must have defined this somewhere
data ConstId a b = ConstId { unConstId :: b }

type Traversal s t a b = LensLike PolyF  s t a b
type Lens      s t a b = LensLike (,)    s t a b
type Prism     s t a b = LensLike Either s t a b
type Grate     s t a b = LensLike (->)   s t a b
type Getter    s t a b = LensLike (Constrained Copointed) s t a b
type Iso       s t a b = LensLike ConstId s t a b
type Setter    s t a b = LensLike PolyEF  s t a b

-- This is more general than I expected
useOptic :: (Wrapped p f a b -> Wrapped p' f' s t)
         -> p a (f b) -> p' s (f' t)
useOptic t = unwrap . t . Wrapped

instance Applicative f => ProfunctorMap PolyF (Wrapped (->) f) where
  pmap (Wrapped f) = Wrapped $ \case
    UnitF -> pure UnitF
    XF x  -> fmap XF (f x)
    ScaleF a p    -> fmap (ScaleF a) (g f p)
    ProductF p p' -> ProductF <$> g f p <*> g f p'
    SumF e       -> case e of
      Left p   -> fmap (SumF . Left)  (g f p)
      Right p' -> fmap (SumF . Right) (g f p')
   where g :: Applicative f => ((a -> f b) -> PolyF c a -> f (PolyF c b))
         g = useOptic pmap

instance Functor f => ProfunctorMap (,) (Wrapped (->) f) where
  pmap (Wrapped f) = Wrapped (\(c, a) -> fmap ((,) c) (f a))

instance (Choice p, Applicative f) => ProfunctorMap Either (Wrapped p f) where
  pmap (Wrapped p) =
    Wrapped (rmap (either (pure . Left) (fmap Right)) (right' p))

instance (Functor f, Contravariant f)
         => (ProfunctorMap (Constrained Copointed) (Wrapped (->) f)) where
  pmap (Wrapped f) =
    Wrapped (\(Constrained g)
                -> contramap (copoint . unConstrained) (f (copoint g)))

instance (Profunctor p, Functor f) => (ProfunctorMap ConstId (Wrapped p f)) where
  pmap (Wrapped p) = Wrapped (dimap unConstId (fmap ConstId) p)

instance (Applicative f, Distributive f)
         => ProfunctorMap PolyEF (Wrapped (->) f) where
  pmap (Wrapped f) = Wrapped $ \case
    UnitEF  -> pure UnitEF
    XEF x   -> fmap XEF (f x)
    ScaleEF a p   -> fmap (ScaleEF a) (g f p)
    ProductEF p p' -> ProductEF <$> g f p <*> g f p'
    SumEF e -> case e of
      Left p   -> fmap (SumEF . Left)  (g f p)
      Right p' -> fmap (SumEF . Right) (g f p')
    ExpEF h -> fmap ExpEF (distribute (fmap (g f) h))
   where g :: (Applicative f, Distributive f)
           => ((a -> f b) -> PolyEF c a -> f (PolyEF c b))
         g = useOptic pmap


traverseOf :: Applicative f
           => Traversal s t a b
           -> (a -> f b) -> s -> f t
traverseOf = useOptic

traverses :: Applicative f
           => ((a -> f b) -> s -> f t)
           -> Traversal s t a b
traverses = error "Not clear what to fill in here"

lensOf :: Functor f
       => Lens s t a b
       -> (a -> f b) -> s -> f t
lensOf = useOptic

lens :: ProfunctorMap (,) p
     => (s -> a)
     -> (s -> b -> t)
     -> p a b -> p s t
lens get set = dimap (\s -> (set s, get s)) (uncurry ($)) . pmap

prismOf :: (Choice p, Applicative f)
        => Prism s t a b
        -> p a (f b) -> p s (f t)
prismOf = useOptic

getOf :: (Functor f, Contravariant f)
      => Getter s t a b
      -> (a -> f b) -> (s -> f t)
getOf = useOptic

isoOf :: (Profunctor p, Functor f)
      => Iso s t a b
      -> p a (f b) -> p s (f t)
isoOf = useOptic

fmapIOf :: (Applicative f, Distributive f)
        => Setter s t a b
        -> (a -> f b) -> (s -> f t)
fmapIOf = useOptic
