{-# LANGUAGE TupleSections #-}


import           Control.Applicative
import qualified Data.Sequence                 as S
import           Control.Arrow                  ( first
                                                , second
                                                )

type R = Float

data DF a = DF Float (L Float a)

newtype L a b = L { runL :: a -> b -> b }

runDF :: Float -> a -> DF a -> (Float, a)
runDF y z (DF x f) = (x, runL f y z)

instance Num (DF a) where
  (+) = (.+)
  (*) = (.*)
  (-) = (.-)
  abs = undefined
  signum = undefined
  fromInteger n = DF (fromInteger n) zero

instance VectorSpace a => VectorSpace (L a b) where
  v1 ..+ v2 = L (\a -> runL v1 a . runL v2 a)
  negateV v = L (\a -> runL v (negateV a))
  r ..* v = L (\a -> runL v (r ..* a))
  zero = L (const id)

instance VectorSpace a => Fractional (DF a) where
  (/) = (./)
  fromRational r = DF (fromRational r) zero

class VectorSpace v where
  (..+)   :: v -> v -> v
  (..-)   :: v -> v -> v
  (..-) v1 v2 = v1 ..+ negateV v2
  (..*)   :: R -> v -> v
  zero    :: v
  negateV :: v -> v
  negateV v = zero ..- v

instance VectorSpace Float where
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
instance (VectorSpace a, VectorSpace b) => VectorSpace (a, b) where
  (v1a, v1b) ..+ (v2a, v2b) = (v1a ..+ v2a, v1b ..+ v2b)
  (v1a, v1b) ..- (v2a, v2b) = (v1a ..- v2a, v1b ..- v2b)
  r ..* (v2a, v2b) = (r ..* v2a, r ..* v2b)
  zero = (zero, zero)

(.+) :: DF a -> DF a -> DF a
(.+) (DF x ddx) (DF y ddy) = DF (x + y) (ddx ..+ ddy)

(.*) :: DF a -> DF a -> DF a
(.*) (DF x ddx) (DF y ddy) = DF (x * y) ((y ..* ddx) ..+ (x ..* ddy))

(.-) :: DF a -> DF a -> DF a
(.-) (DF x ddx) (DF y ddy) = DF (x - y) (ddx ..- ddy)

(./) :: DF a -> DF a -> DF a
(./) (DF x ddx) (DF y ddy) =
  DF (x / y) (((1 / y) ..* ddx) ..- ((x / (y * y)) ..* ddy))

f :: VectorSpace a => (DF a, DF a) -> DF a
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
foo t = (runDF 1 (mapT (const 0) t) . f . mapT wrap . modifyAllT) t

wrap :: (Float, (Float -> Float) -> a -> a) -> DF a
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

mapT :: (a -> b) -> (a, a) -> (b, b)
mapT f (a, b) = (f a, f b)

prod :: S.Seq (DF a) -> DF a
prod = foldl (*) 1

runProd :: S.Seq Float -> (Float, S.Seq Float)
runProd t = (runDF 1 (fmap (const 0) t) . prod . fmap wrap . modifyAllSeq) t

enumerate :: S.Seq a -> S.Seq (Int, a)
enumerate = S.drop 1 . S.scanl (\(i, _) b -> (i + 1, b)) (-1, undefined)
