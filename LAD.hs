{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# OPTIONS_GHC -Wno-missing-methods #-}


import qualified Data.Functor.Identity         as I
import qualified Data.Sequence                 as S
import           Control.Arrow                  ( first
                                                , second
                                                )
import           Data.VectorSpace

-- An extremely general and simple presentation of automatic
-- differentiation

-- Define a type that allows us to attach a vector to a value.
-- Mathematical operations on `D`s will operate on the value and also
-- on the vector attached to it.  The operations on the vector will
-- amount to different ways of calculating the derivative.
data D v a = D a v

-- Implement mathematical functions for `D`.  This amounts to
-- reimplementing the original function and additionally providing its
-- derivative.
instance (Scalar s ~ a, VectorSpace s, Num a) => Num (D s a) where
  (+) (D x dx) (D y dy) = D (x + y) (dx ^+^ dy)
  (*) (D x dx) (D y dy) = D (x * y) (y *^ dx ^+^ x *^ dy)
  (-) (D x dx) (D y dy) = D (x - y) (dx ^-^ dy)
  abs (D x dx) = D (abs x) (signum x *^ dx)
  signum (D x _) = D (signum x) zeroV
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


-- Automatic differentiation

-- The vector attached to `D` is completely abstract so we can
-- interpret it in different ways.  Both forward and reverse mode AD
-- fall straight out of this setup by instantiating the vector at
-- different types.

-- Forward mode

-- A type to carry around the necessary data for forward mode.  This
-- is equivalent to the "dual number" from classical presentations of
-- forward mode AD.
type Forward s a = D (I s) a

-- For slightly annoying typeclass-related reasons we need an
-- auxiliary wrapper type.
newtype I a = I { unI :: a } deriving Num

-- The implementation of ad's `diffF'` is straightforward

-- cf. https://hackage.haskell.org/package/ad-4.3.6/docs/Numeric-AD.html#v:diffF-39-
diffF'
  :: (Functor f, Num a) => ((Forward a a -> f (Forward a a)) -> a -> f (a, a))
diffF' f a = fmap (\(D b1 b2) -> (b1, unI b2)) (f (D a 1))

diffF'example :: Floating a => [(a, a)]
diffF'example = diffF' (\a -> [sin a, cos a]) 0

-- > diffF'example
-- [(0.0,1.0),(1.0,-0.0)]

-- The instances for our auxiliary type
instance Num a => AdditiveGroup (I a) where
  I v1 ^+^ I v2 = I (v1 + v2)
  negateV (I v) = I (-v)
  zeroV = I 0

instance Num a => VectorSpace (I a) where
  type Scalar (I a) = a
  r *^ (I v) = I (r * v)

-- Reverse mode

-- Suprisingly, reverse mode also falls straight out of this setup

-- A type to carry around the necessary data for reverse mode.  Recall
-- that the first parameter to D can be an arbitrary vector space.
type Reverse s a = D (L a s) a

-- What is the `L a s` parameter?  It's this somewhat mysterious
-- construction.
newtype L a b = L { runL :: a -> b -> b }

-- It has the structure of a VectorSpace [1].  This structure is
-- rather intriguing and the key to implementing reverse mode.
--
-- `L a b` plays the role of the "Wengert list" from classical
-- presentations of reverse mode AD.  As evaluation proceeds we
-- encounter values of type `L a b`.  We unwrap each and apply a value
-- of type `a` giving us a `b -> b`.  This is essentially an entry to
-- be written onto the Wengert list, or perhaps more accurately a
-- closure containing the entry and performing the appropriate action
-- with it.  The implementation of `^+^` composes these entries
-- together, essentially writing consecutive entries onto the list.
-- When we have finished building the "list" we apply our function `b
-- -> b` to a value of type `b` which corresponds to performing the
-- backward pass, walking the list and accumulating the derivatives.
instance Num a => AdditiveGroup (L a b) where
  v1 ^+^ v2 = L (\a -> runL v1 a . runL v2 a)
  negateV v = L (\a -> runL v (-a))
  zeroV = L (const id)

instance Num a => VectorSpace (L a b) where
  type Scalar (L a b) = a
  r *^ v = L (\a -> runL v (r * a))

-- The implementation of ad's `grad'` and `jacobian'` are
-- straightforward.  I am complicating the types of the most general
-- versions whilst I work out the best way to proceed.  The
-- list-specialised versions are simpler to understand.

-- cf. https://hackage.haskell.org/package/ad-4.3.6/docs/Numeric-AD.html#v:grad-39-
grad'List :: Num a => ([Reverse [a] a] -> Reverse [a] a) -> [a] -> (a, [a])
grad'List = grad' fmap fmap modifyAllList

-- cf. https://hackage.haskell.org/package/ad-4.3.6/docs/Numeric-AD.html#v:jacobian-39-
jacobian'List
  :: (Functor g, Num a)
  => ([Reverse [a] a] -> g (Reverse [a] a))
  -> [a]
  -> g (a, [a])
jacobian'List = jacobian' fmap fmap fmap modifyAllList

-- Feel free to skip the complicated general versions whilst I work
-- out how best to present them.
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
  I.runIdentity (jacobian' mapit1 mapit2 fmap mait (I.Identity . f) t)

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
 where
  zeros = mapit1 (const 0) t
  wrap  = \(a, s) -> D a (L (\b -> s (+ b)))
  runReverse :: a -> s -> Reverse s a -> (a, s)
  runReverse y z (D x g) = (x, runL g y z)

grad'Example1 :: Num a => (a, [a])
grad'Example1 = grad'List (\[x, y, z] -> x * y + z) [1, 2, 3]

grad'Example2 :: Floating a => (a, [a])
grad'Example2 = grad'List (\[x, y] -> x ** y) [0, 2]

-- > grad'Example1
-- (5,[2,1,1])

-- > grad'Example2
-- (0.0,[0.0,NaN])

jacobian'Example3 :: Num a => [(a, [a])]
jacobian'Example3 = jacobian'List (\[x, y] -> [y, x, x * y]) [2, 1]

-- > jacobian'Example3
-- [(1,[0,1]),(2,[1,0]),(2,[1,2])]

-- Higher derivatives

-- We can take the results of differentiating and differentiate
-- further, calculating higher order derivatives.

-- Here's a function to take the gradient of a function single
-- variable, single output function
grad1 :: Num a => (Reverse a a -> Reverse a a) -> a -> a
grad1 x = snd . grad' id id (\y -> (y, id)) x

-- We can differentiate the `square` function twice.  Since `square x
-- = x * x`, `square' x` should be `2 * x` and `square''` should be
-- `2`.
square :: Num a => a -> a
square x = x * x

square' :: Num a => a -> a
square' = grad1 square

square'' :: Num a => a -> a
square'' = grad1 square'

-- > map square' [0..10]
-- [0,2,4,6,8,10,12,14,16,18,20]

-- > map square'' [0..10]
-- [2,2,2,2,2,2,2,2,2,2,2]

-- ad and backprop use an ST-like higher-rank running function for two
-- reasons.  Firstly, it's supposedly safer and stops variables
-- escaping to places they shouldn't be, but secondly, I think they
-- are forced to by their implementation.  We aren't.  This allows us
-- to express strange things.
--
-- Will it lead to perturbation confusion?  Perhaps not, because we
-- don't have any way of combining a `Reverse a a` with an `a`.
perturbationConfusion :: Num a => Reverse a a -> a -> a
perturbationConfusion y = grad1 (\x -> x * y)

-- Performance

-- I believe we are doing genuine reverse mode AD because we seem to
-- have run time linear in the number of inputs.  For example, we can
-- take the product of a large number of variables.

prod :: Num a => S.Seq a -> a
prod = foldl (*) 1

gradProd :: S.Seq Float -> (Float, S.Seq Float)
gradProd = grad' mapit1 mapit2 mait prod
 where
  mapit1 = fmap
  mapit2 = fmap
  mait   = modifyAllSeq

-- If we run it on `n` inputs we can see it runs in time O(`n`).
gradProdOn :: Int -> ()
gradProdOn n = snd (gradProd (S.replicate n 1)) `seq` ()

-- > gradProdOn 200000
-- 2.52 secs
-- > gradProdOn 800000
-- 10.76 secs
-- > gradProdOn 1600000
-- 21.68 secs


-- Another example

-- Let's take a simple arithmetic function

f_primal :: Fractional a => (a, a) -> a
f_primal (x, y) =
  let p = 7 * x
      r = 1 / y
      q = p * x * 5
      v = 2 * p * q + 3 * r
  in  v

-- The handwritten reverse mode derivative follows

f_rev_hand :: Fractional a => (a, a) -> (a, (a, a))
f_rev_hand (x, y) =
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
  in  (v, (dα_dx, dα_dy))

-- And the automatically generated reverse mode derivative is

f_rev_ad :: Fractional a => (a, a) -> (a, (a, a))
f_rev_ad = grad' mapit1 mapit2 mait f_primal
 where
  mapit1 = mapT
  mapit2 = mapT
  mait   = modifyAllT

-- Let's check the two reverse mode functions are equal.  Running
-- test_f shows that they are equal on all the points we sample.

test_f :: IO ()
test_f = flip mapM_ samples $ \t -> do
  print (f_rev_ad t)
  print (f_rev_hand t)
  putStrLn ""
  where samples = (,) <$> [1 :: Float .. 4] <*> [1 .. 4]


-- Some cruft for a flat ending

modifyAllT
  :: (a, a)
  -> ((a, (b -> b) -> (b, b) -> (b, b)), (a, (b -> b) -> (b, b) -> (b, b)))
modifyAllT (a, b) = ((a, first), (b, second))

modifyAllSeq :: S.Seq t -> S.Seq (t, (a -> a) -> S.Seq a -> S.Seq a)
modifyAllSeq = fmap (\(i, a) -> (a, flip S.adjust i)) . enumerate

modifyAllList :: [t] -> [(t, (a -> a) -> [a] -> [a])]
modifyAllList = fmap (\(i, a) -> (a, modifyAt i)) . zip [0 ..]
 where
  modifyAt i f xs =
    zipWith (\j x -> if i == j then f x else x) [0 :: Integer ..] xs

mapT :: (a -> b) -> (a, a) -> (b, b)
mapT f (a, b) = (f a, f b)


enumerate :: S.Seq a -> S.Seq (Int, a)
enumerate = S.drop 1 . S.scanl (\(i, _) b -> (i + 1, b)) (-1, undefined)

-- [1] We need to restrict ourselves to a subset of `L a s` in order
-- to ensure the vector space laws are followed.  I'll have to write
-- more about that later, but I don't think it's terribly interesting.
-- It's probably just the subset of elements of the form `L ((+)
-- . phi)` for some linear map `phi`.
