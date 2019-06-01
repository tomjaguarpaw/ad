{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-missing-methods #-}


import           Control.Applicative
import qualified Data.Sequence                 as S
import           Control.Arrow                  ( first
                                                , second
                                                )
import           Data.VectorSpace

data D v a = D a v

type Reverse s a = D (L a s) a
type Forward a = D a a

newtype L a b = L { runL :: a -> b -> b }

runReverse :: a -> s -> Reverse s a -> (a, s)
runReverse y z (D x f) = (x, runL f y z)

instance (Scalar s ~ a, VectorSpace s, Num a) => Num (D s a) where
  (+) (D x dx) (D y dy) = D (x + y) (dx ^+^ dy)
  (*) (D x dx) (D y dy) = D (x * y) (y *^ dx ^+^ x *^ dy)
  (-) (D x dx) (D y dy) = D (x - y) (dx ^-^ dy)
  abs = undefined
  signum = undefined
  fromInteger n = D (fromInteger n) zeroV

instance (Scalar s ~ a, VectorSpace s, Fractional a) => Fractional (D s a) where
  (/) (D x dx) (D y dy) =
    D (x / y) ((1 / y) *^ dx ^-^ (x / (y * y)) *^ dy)
  fromRational r = D (fromRational r) zeroV

instance (Scalar s ~ a, VectorSpace s, Floating a) => Floating (D s a) where
  (**) (D x dx) (D y dy) =
    let z = x ** y
    in  D z ((y * x ** (y - 1)) *^ dx ^+^ (log x * z) *^ dy)
  sin (D x dx) = D (sin x) (cos x *^ dx)
  cos (D x dx) = D (cos x) ((-sin x) *^ dx)

instance Num a => AdditiveGroup (L a b) where
  v1 ^+^ v2 = L (\a -> runL v1 a . runL v2 a)
  negateV v = L (\a -> runL v (-a))
  zeroV = L (const id)

instance Num a => VectorSpace (L a b) where
  type Scalar (L a b) = a
  r *^ v = L (\a -> runL v (r * a))

f :: Fractional a => (a, a) -> a
f (x, y) =
  let p = 7 * x
      r = 1 / y
      q = p * x * 5
      v = 2 * p * q + 3 * r
  in  v

fhand :: Fractional a => (a, a) -> (a, a)
fhand (x, y) =
  let dα_dv = 1

      p     = 7 * x
      r     = 1 / y
      q     = p * x * 5
      v     = 2 * p * q + 3 * r

      dv_dq = 2 * p

      dα_dq = dα_dv * dv_dq

      dq_dr = 0
      dv_dr = 3

      dα_dr = dα_dq * dq_dr + dα_dv * dv_dr

      dr_dp = 0
      dq_dp = x * 5
      dv_dp = 2 * q

      dα_dp = dα_dr * dr_dp + dα_dq * dq_dp + dα_dv * dv_dp

      dv_dx = 0
      dv_dy = 0

      dr_dx = 0
      dr_dy = -1 / (y * y)

      dq_dx = p * 5
      dq_dy = 0

      dp_dx = 7
      dp_dy = 0

      dα_dx = dα_dp * dp_dx + dα_dq * dq_dx + dα_dr * dr_dx + dα_dv * dv_dx
      dα_dy = dα_dp * dp_dy + dα_dq * dq_dy + dα_dr * dr_dy + dα_dv * dv_dy
  in  (dα_dx, dα_dy)

foo :: Fractional a => (a, a) -> (a, (a, a))
foo = grad' mapit1 mapit2 mait f
 where
  mapit1 = mapT
  mapit2 = mapT
  mait   = modifyAllT

testf :: Fractional a => (a, a) -> ((a, a), (a, a))
testf t = (snd (foo t), fhand t)

wrap :: Num a => (a, (a -> a) -> s -> s) -> Reverse s a
wrap = \(a, s) -> D a (L (\a -> s (+ a)))

modifyAllT
  :: Num b
  => (a, a)
  -> ( (a, (b -> b) -> (b, b) -> (b, b))
     , (a, (b -> b) -> (b, b) -> (b, b))
     )
modifyAllT (a, b) = ((a, first), (b, second))

modifyAllSeq :: S.Seq t -> S.Seq (t, (a -> a) -> S.Seq a -> S.Seq a)
modifyAllSeq = fmap (\(i, a) -> (a, flip S.adjust i)) . enumerate

modifyAllList :: [t] -> [(t, (a -> a) -> [a] -> [a])]
modifyAllList = fmap (\(i, a) -> (a, modifyAt i)) . zip [0 ..]
  where modifyAt i f xs = zipWith (\j x -> if i == j then f x else x) [0 ..] xs

mapT :: (a -> b) -> (a, a) -> (b, b)
mapT f (a, b) = (f a, f b)

prod :: Num a => S.Seq a -> a
prod = foldl (*) 1

runProd :: S.Seq Float -> (Float, S.Seq Float)
runProd = grad' mapit1 mapit2 mait prod
 where
  mapit1 = fmap
  mapit2 = fmap
  mait   = modifyAllSeq

grad'
  :: Num a
  => ((s_ -> a) -> fs -> fa)
  -> (  ((a, (a -> a) -> s' -> s') -> Reverse s' a)
     -> fsselect
     -> fReversefaa
     )
  -> (fs -> fsselect)
  -> (fReversefaa -> Reverse fa a)
  -> fs
  -> (a, fa)
grad' mapit1 mapit2 mait f t =
  (runReverse 1 (mapit1 (const 0) t) . f . mapit2 wrap . mait) t

jacobian'
  :: Num a
  => ((s -> a) -> fs -> fa)
  -> (  ((a, (a -> a) -> fs' -> fs') -> Reverse fs' a)
     -> fsselect
     -> fReversefaa
     )
  -> ((Reverse fa a -> (a, fa)) -> gReversefaa -> g (a, fa))
  -> (fs -> fsselect)
  -> (fReversefaa -> gReversefaa)
  -> fs
  -> g (a, fa)
jacobian' mapit1 mapit2 mapit3 mait f t =
  (mapit3 (runReverse 1 zeros) . f . mapit2 wrap . mait) t
  where zeros = mapit1 (const 0) t

-- The derived type signature is much more general
diffF'G
  :: Num a
  => ((Forward a -> (a, a)) -> fForwarda -> faa)
  -> (Forward a -> fForwarda)
  -> a
  -> faa
diffF'G mapit f a = mapit (\(D a a') -> (a, a')) (f (D a 1))

diffF' :: (Num a, Functor f) => (Forward a -> f (Forward a)) -> a -> f (a, a)
diffF' = diffF'G fmap

adExample :: Num a => (a, [a])
adExample = grad' fmap fmap modifyAllList (\[x, y, z] -> x * y + z) [1, 2, 3]

adExample2 :: Floating a => (a, [a])
adExample2 = grad' fmap fmap modifyAllList (\[x, y] -> x ** y) [0, 2]

adExample3 :: Num a => [(a, [a])]
adExample3 =
  jacobian' fmap fmap fmap modifyAllList (\[x, y] -> [y, x, x * y]) [2, 1]

adExample4 :: [(Float, Float)]
adExample4 = diffF' (\a -> [sin a, cos a]) 0

enumerate :: S.Seq a -> S.Seq (Int, a)
enumerate = S.drop 1 . S.scanl (\(i, _) b -> (i + 1, b)) (-1, undefined)

once :: Num a => a -> a
once = snd . grad' id id (\x -> (x, id)) (\x -> x * x)

twice :: Num a => a -> a
twice = snd . grad' id id (\x -> (x, id)) once

perturbationConfusion :: Num a => Reverse a a -> a -> a
perturbationConfusion y = snd . grad' id id (\x -> (x, id)) (\x -> x * y)
