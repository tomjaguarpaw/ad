{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs      #-}
{-# LANGUAGE DataKinds  #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -Wall #-}

import Data.Profunctor
import Data.Functor.Const

-- A polynomial in a single variable X over ring a
data Poly a =
    Unit
  | X
  | Scale a (Poly a)
  | Product (Poly a) (Poly a)
  | Sum (Poly a) (Poly a)

-- A polynomial functor (with shape p)
data PolyF p x where
  UnitF    :: PolyF 'Unit x
  XF       :: x -> PolyF 'X x
  ScaleF   :: a -> PolyF p x -> PolyF ('Scale a p) x
  ProductF :: PolyF p x -> PolyF p' x -> PolyF ('Product p p') x
  SumF     :: Either (PolyF p x) (PolyF p' x) -> PolyF ('Sum p p') x

class Profunctor p => ProfunctorMap (f :: k -> * -> *) p where
  pmap :: p a b -> p (f c a) (f c b)

data Wrapped p f a b = Wrapped { unwrap :: p a (f b) }

instance (Profunctor p, Functor f) => Profunctor (Wrapped p f) where
  dimap g h (Wrapped f) = Wrapped (dimap g (fmap h) f)

type LensLike f s t a b = forall p. ProfunctorMap f p => p a b -> p s t

type Traversal s t a b = LensLike PolyF  s t a b
type Lens      s t a b = LensLike (,)    s t a b
type Prism     s t a b = LensLike Either s t a b
type Grate     s t a b = LensLike (->)   s t a b
type Getter    s t a b = LensLike Const  s t a b

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

traverseOf :: Applicative f
           => Traversal s t a b
           -> (a -> f b) -> s -> f t
traverseOf = useOptic

lensOf :: Functor f
       => Lens s t a b
       -> (a -> f b) -> s -> f t
lensOf = useOptic

prismOf :: (Choice p, Applicative f)
        => Prism s t a b
        -> p a (f b) -> p s (f t)
prismOf = useOptic
