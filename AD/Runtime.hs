{-# LANGUAGE NoMonomorphismRestriction #-}

module Runtime where

import Data.Vector as V

type Vec a = V.Vector a
type Mat a = Vec (Vec a)

size = V.length

build = V.generate

build2 m n f = build m (build n . f)

sum :: Num a => Vector a -> a
sum = V.sum

mul :: Num a => Mat a -> Vec a -> Vec a
mul a b = Runtime.vsum (build (size a) (\i -> (a ! i) `vmul` (b ! i)))

vmul :: Num a => Vec a -> a -> Vec a
vmul a b = build (size a) (\i -> a ! i * b)

vsum :: Num a => Vec (Vec a) -> Vec a
vsum a = build (size (a ! 0)) (\i ->
           Runtime.sum (build (size a) (\j -> a ! j ! i)))

max :: Ord a => Vector a -> a
max = V.maximum

expv = V.map exp

sqnorm = Runtime.sum . V.map square
  where square x = x * x

gammaLn :: a -> a
gammaLn = id

a `minus` b = build (size a) (\i -> a ! i - b)

sub :: Num a => Vector a -> Vector a -> Vector a
a `sub` b = build (size a) (\i -> a ! i - b ! i)
