{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-missing-methods #-}


import           Control.Applicative
import qualified Data.Sequence                 as S
import           Control.Arrow                  ( first
                                                , second
                                                )
import           Data.VectorSpace

type R = Float

data DV v a = DF a v

type DF s a = DV (L a s) a

newtype L a b = L { runL :: a -> b -> b }

runDF :: a -> s -> DF s a -> (a, s)
runDF y z (DF x f) = (x, runL f y z)

instance (Scalar s ~ a, VectorSpace s, Num a) => Num (DV s a) where
  (+) (DF x dx) (DF y dy) = DF (x + y) (dx ^+^ dy)
  (*) (DF x dx) (DF y dy) = DF (x * y) (y *^ dx ^+^ x *^ dy)
  (-) (DF x dx) (DF y dy) = DF (x - y) (dx ^-^ dy)
  abs (DF x l) = undefined
  signum = undefined
  fromInteger n = DF (fromInteger n) zeroV

instance (Scalar s ~ a, VectorSpace s, Fractional a) => Fractional (DV s a) where
  (/) (DF x dx) (DF y dy) =
    DF (x / y) ((1 / y) *^ dx ^-^ (x / (y * y)) *^ dy)
  fromRational r = DF (fromRational r) zeroV

instance (Scalar s ~ a, VectorSpace s, Floating a) => Floating (DV s a) where
  (**) (DF x dx) (DF y dy) =
    let z = x ** y
    in  DF z ((y * x ** (y - 1)) *^ dx ^+^ (log x * z) *^ dy)

instance Num a => AdditiveGroup (L a b) where
  v1 ^+^ v2 = L (\a -> runL v1 a . runL v2 a)
  negateV v = L (\a -> runL v (-a))
  zeroV = L (const id)

instance Num a => VectorSpace (L a b) where
  type Scalar (L a b) = a
  r *^ v = L (\a -> runL v (r * a))

f :: (Fractional a, VectorSpace s) => (DF s a, DF s a) -> DF s a
f (x, y) =
  let p = 7 * x
      r = 1 / y
      q = p * x * 5
      v = 2 * p * q + 3 * r
  in  v

fhand :: Fractional a => a -> a -> (a, a)
fhand x y =
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

foo :: (Float, Float) -> (Float, (Float, Float))
foo = grad' mapit1 mapit2 mait f
 where
  mapit1 = mapT
  mapit2 = mapT
  mait   = modifyAllT

wrap :: Num a => (a, (a -> a) -> s -> s) -> DF s a
wrap = \(a, s) -> DF a (L (\a -> s (+ a)))

modifyAllT
  :: Num b
  => (a, a)
  -> ( (a, (b -> b) -> (b, b) -> (b, b))
     , (a, (b -> b) -> (b, b) -> (b, b))
     )
modifyAllT (a, b) = ((a, first), (a, second))

modifyAllSeq :: S.Seq t -> S.Seq (t, (a -> a) -> S.Seq a -> S.Seq a)
modifyAllSeq = fmap (\(i, a) -> (a, flip S.adjust i)) . enumerate

modifyAllList :: [t] -> [(t, (a -> a) -> [a] -> [a])]
modifyAllList = fmap (\(i, a) -> (a, modifyAt i)) . zip [0 ..]
  where modifyAt i f xs = zipWith (\j x -> if i == j then f x else x) [0 ..] xs

mapT :: (a -> b) -> (a, a) -> (b, b)
mapT f (a, b) = (f a, f b)

prod :: Num a => S.Seq (DF s a) -> DF s a
prod = foldl (*) 1

runProd :: S.Seq Float -> (Float, S.Seq Float)
runProd = grad' mapit1 mapit2 mait prod
 where
  mapit1 = fmap
  mapit2 = fmap
  mait   = modifyAllSeq

grad'
  :: Num a
  => ((a_ -> a) -> ffloat -> ffloat')
  -> (  ((a, (a -> a) -> ffloat'' -> ffloat'') -> DF ffloat'' a)
     -> ffloatselect
     -> fdffloat
     )
  -> (ffloat -> ffloatselect)
  -> (fdffloat -> DF ffloat' a)
  -> ffloat
  -> (a, ffloat')
grad' mapit1 mapit2 mait f t =
  (runDF 1 (mapit1 (const 0) t) . f . mapit2 wrap . mait) t

jacobian'
  :: Num a
  => ((float -> a) -> ffloat -> ffloat')
  -> (  ((a, (a -> a) -> ffloat'' -> ffloat'') -> DF ffloat'' a)
     -> ffloatselect
     -> fdffloat
     )
  -> (  (DF ffloat' a -> (a, ffloat'))
     -> g (DF ffloat' a)
     -> g (a, ffloat')
     )
  -> (ffloat -> ffloatselect)
  -> (fdffloat -> g (DF ffloat' a))
  -> ffloat
  -> g (a, ffloat')
jacobian' mapit1 mapit2 mapit3 mait f t =
  (mapit3 (runDF 1 zeros) . f . mapit2 wrap . mait) t
  where zeros = mapit1 (const 0) t

adExample :: (Float, [Float])
adExample = grad' fmap fmap modifyAllList (\[x, y, z] -> x * y + z) [1, 2, 3]

adExample2 :: (Float, [Float])
adExample2 = grad' fmap fmap modifyAllList (\[x, y] -> x ** y) [0, 2]

adExample3 =
  jacobian' fmap fmap fmap modifyAllList (\[x, y] -> [y, x, x * y]) [2, 1]

enumerate :: S.Seq a -> S.Seq (Int, a)
enumerate = S.drop 1 . S.scanl (\(i, _) b -> (i + 1, b)) (-1, undefined)

once :: Num a => a -> a
once = snd . grad' id id (\x -> (x, id)) (\x -> x * x)

twice :: Num a => a -> a
twice = snd . grad' id id (\x -> (x, id)) once
