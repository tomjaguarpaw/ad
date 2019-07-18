{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE DeriveFoldable    #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase        #-}

import           Data.Foldable        hiding (mapM_)
import qualified Data.Maybe           as Maybe
import qualified Data.Map.Strict      as Map
import           Data.Functor.Compose (Compose(Compose, getCompose))
import           Control.Monad.Free   (Free(Pure, Free), iter)

-- { Boring

type Coord = Int
type V = Map.Map Coord Double

-- The zero vector
zero :: V
zero = Map.fromList (zip [1..1000] [0,0..])

-- Add two vectors
plus :: V -> V -> V
plus = Map.unionWith (+)

-- Multiply a vector by a scalar
times :: Double -> V -> V
times a = Map.map (a *)

-- Negate a vector
negateV :: V -> V
negateV = Map.map negate

-- The component of a vector in a given coordinate direction.
-- For example, the "component along" 2 of (3,4,5,6,...) is 4.
componentAlong :: Coord -> V -> Double
componentAlong i v = Maybe.fromMaybe 0 (Map.lookup i v)

-- A vector which has one non-zero entry, value x in the i
-- direction.  For example, "5 `inDirection` 3" is (0,0,5,0,...).
inDirection :: Double -> Coord -> V
inDirection x i = Map.fromList [(i, x)]

-- Add a quantity to the given component.  For example,
-- "plusComponent 2 10 (3,4,5,6,...)" is "(3,14,5,6,...)".
plusComponent :: Coord -> Double -> V -> V
plusComponent = Map.insertWith (+)

-- }

data F r = Zero
         | One
         | Negate r
         | Sum r r
         | Product r r
         | Exp r
         deriving (Functor, Foldable)

eval :: F Double -> Double
eval = \case
  Zero        -> 0
  One         -> 1
  Negate  x   -> -x
  Sum     x y -> x + y
  Product x y -> x * y
  Exp     x   -> exp x

diff :: F (Double, r) -> [(Double, r)]
diff = \case
  Zero                    -> zero_
  One                     -> zero_
  Negate  (_, dx)         -> (-1) .* dx
  Sum     (_, dx) (_, dy) -> (1 .* dx) .+ (1 .* dy)
  Product (x, dx) (y, dy) -> (y .* dx) .+ (x .* dy)
  Exp     (x, dx)         -> exp x .* dx
  where x .* y = [(x, y)]
        (.+)   = (++)
        zero_   = []

type E    = Free F
type EL a = Free (Compose F ((,) a))

forwardMode :: V -> E Coord -> (Double, V)
forwardMode v = iter g . fmap f
  where f i = (componentAlong i v,
               1 `inDirection` i)

        g u = (eval' u, d u)

        sumV = foldl' plus zero

        d :: F (Double, V) -> V
        d = sumV
            . fmap (uncurry times)
            . diff
                         
        eval' :: F (Double, V) -> Double
        eval' = eval . fmap fst

func :: E a -> E a
func x = exp_ (x_ `minus` one)
  where a `minus` b = Free (a `Sum` Free (Negate b))
        one         = Free One
        x_          = x
        exp_ a      = Free (Exp a)
        
bigExpression :: E Coord
bigExpression = iterate func x1 !! 1000
  where x1 = Pure 1

exampleForward :: IO ()
exampleForward =
  mapM_ (print
         . componentAlong 1
         . snd
         . flip forwardMode bigExpression
         . (`inDirection` 1))
        [0.00009, 1, 1.00001]

evalDecorate :: V
             -> E Coord
             -> (Double, EL Double Coord)
evalDecorate v = iter g . fmap f
  where f i = (componentAlong i v, Pure i)
        g u = let eval' = eval . fmap fst
                  id'   = Free . Compose
              in (eval' u, id' u)

sensitivityDecorate :: Double
                    -> EL Double coord
                    -> Free [] (Double, coord)
sensitivityDecorate s = \case
  Pure x -> Pure (s, x)
  Free f -> (Free
             . fmap (\(d, e) -> sensitivityDecorate (s * d) e)
             . diff
             . getCompose)
            f

reverseMode :: V -> E Coord -> V
reverseMode v = foldl' (\d (s, x) -> plusComponent x s d) zero
                . sensitivityDecorate 1
                . snd
                . evalDecorate v

exampleReverse :: IO ()
exampleReverse =
  mapM_ (print
         . componentAlong 1
         . flip reverseMode bigExpression
         . (`inDirection` 1))
        [0.00009, 1, 1.00001]
