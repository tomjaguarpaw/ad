{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-missing-methods #-}


import           Control.Applicative
import qualified Data.Sequence                 as S
import           Control.Arrow                  ( first
                                                , second
                                                )

type R = Float

data DF s a = DF s (L s a)

newtype L a b = L { runL :: a -> b -> b }

runDF :: s -> a -> DF s a -> (s, a)
runDF y z (DF x f) = (x, runL f y z)

instance Num s => Num (DF s a) where
  (+) = (.+)
  (*) = (.*)
  (-) = (.-)
  abs = undefined
  signum = undefined
  fromInteger n = DF (fromInteger n) zero

instance Num a => VectorSpace (L a b) where
  type Scalar (L a b) = a
  v1 ..+ v2 = L (\a -> runL v1 a . runL v2 a)
  negateV v = L (\a -> runL v (-a))
  r ..* v = L (\a -> runL v (r * a))
  zero = L (const id)

instance Fractional s => Fractional (DF s a) where
  (/) = (./)
  fromRational r = DF (fromRational r) zero

instance Floating s => Floating (DF s a) where
  (**) = (.**)

class VectorSpace v where
  type Scalar v
  (..+)   :: v -> v -> v
  (..-)   :: v -> v -> v
  (..-) v1 v2 = v1 ..+ negateV v2
  (..*)   :: Scalar v -> v -> v
  zero    :: v
  negateV :: v -> v
  negateV v = zero ..- v

instance VectorSpace Float where
  type Scalar Float = Float
  (..+) = (+)
  (..-) = (-)
  (..*) = (*)
  zero  = 0
  negateV = negate
{-
instance VectorSpace b => VectorSpace (a -> b) where
  (..+) = liftA2 (..+)
  (..-) = liftA2 (..-)
  (..*) r = liftA ((..*) r)
  zero = pure zero
-}
instance (Scalar a ~ Scalar b, VectorSpace a, VectorSpace b) => VectorSpace (a, b) where
  type Scalar (a, b) = Scalar a
  (v1a, v1b) ..+ (v2a, v2b) = (v1a ..+ v2a, v1b ..+ v2b)
  (v1a, v1b) ..- (v2a, v2b) = (v1a ..- v2a, v1b ..- v2b)
  r ..* (v2a, v2b) = (r ..* v2a, r ..* v2b)
  zero = (zero, zero)

(.+) :: Num s => DF s a -> DF s a -> DF s a
(.+) (DF x ddx) (DF y ddy) = DF (x + y) (ddx ..+ ddy)

(.*) :: Num s => DF s a -> DF s a -> DF s a
(.*) (DF x ddx) (DF y ddy) = DF (x * y) ((y ..* ddx) ..+ (x ..* ddy))

(.-) :: Num s => DF s a -> DF s a -> DF s a
(.-) (DF x ddx) (DF y ddy) = DF (x - y) (ddx ..- ddy)

(./) :: Fractional s => DF s a -> DF s a -> DF s a
(./) (DF x ddx) (DF y ddy) =
  DF (x / y) (((1 / y) ..* ddx) ..- ((x / (y * y)) ..* ddy))

(.**) :: Floating s => DF s a -> DF s a -> DF s a
(.**) (DF x ddx) (DF y ddy) =
  let z = x ** y
  in  DF z (((y * x ** (y - 1)) ..* ddx) ..+ ((log x * z) ..* ddy))

f :: (Fractional s, VectorSpace a) => (DF s a, DF s a) -> DF s a
f (x, y) =
  let p = 7 * x
      r = 1 / y
      q = p * x * 5
      v = 2 * p * q + 3 * r
  in  v

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

wrap :: Num s => (s, (s -> s) -> a -> a) -> DF s a
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

prod :: Num s => S.Seq (DF s a) -> DF s a
prod = foldl (*) 1

runProd :: S.Seq Float -> (Float, S.Seq Float)
runProd = grad' mapit1 mapit2 mait prod
 where
  mapit1 = fmap
  mapit2 = fmap
  mait   = modifyAllSeq

grad'
  :: Num s
  => ((s_ -> s) -> ffloat -> ffloat')
  -> (  ((s, (s -> s) -> ffloat'' -> ffloat'') -> DF s ffloat'')
     -> ffloatselect
     -> fdffloat
     )
  -> (ffloat -> ffloatselect)
  -> (fdffloat -> DF s ffloat')
  -> ffloat
  -> (s, ffloat')
grad' mapit1 mapit2 mait f t =
  (runDF 1 (mapit1 (const 0) t) . f . mapit2 wrap . mait) t

jacobian'
  :: Num s
  => ((float -> s) -> ffloat -> ffloat')
  -> (  ((s, (s -> s) -> ffloat'' -> ffloat'') -> DF s ffloat'')
     -> ffloatselect
     -> fdffloat
     )
  -> (  (DF s ffloat' -> (s, ffloat'))
     -> g (DF s ffloat')
     -> g (s, ffloat')
     )
  -> (ffloat -> ffloatselect)
  -> (fdffloat -> g (DF s ffloat'))
  -> ffloat
  -> g (s, ffloat')
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
