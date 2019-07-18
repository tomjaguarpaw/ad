{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}

module GMM where

import Runtime as R
import Data.Vector as V
import Data.Traversable

logsumexp :: (Ord a, Floating a) => Vector a -> a
logsumexp a =
  let mx = R.max a
      semx = R.sum (expv (a `R.minus` mx))
  in log semx + mx

log_gamma_distrib :: Floating a => a -> Int -> a
log_gamma_distrib a p =
    log (fromIntegral p ** (0.25*(fromIntegral (p*(p-1))))) + 
    R.sum (build p (\j -> gammaLn (a + 0.5*(1 - (fromIntegral j)))))

---------- Gaussian Mixture Model (GMM) ----------

-- Nth triangular number
tri :: Int -> Int
tri n = n * (n - 1) `div` 2

-- Create lower triangular matrix from log-diagonal and lower triangle
makeQ :: Floating a => Vector a -> Vector a -> Vector (Vector a)
makeQ q l =
  let d = size q
  in  build2 d d (\i j ->
                     if i < j then
                       0.0
                     else if i == j then
                       exp (q ! i)
                     else
                       l ! (tri (i - 1) + j)
                 )

-- Negative log likelihood of GMM
gmm_objective :: (Floating a, Ord a)
              => Mat a -> Vec a -> Mat a -> Mat a -> Mat a -> a
gmm_objective x alphas means qs ls =
    let n  = R.size x
        kk = size alphas
    in R.sum ( build n (\i ->
          logsumexp( build kk (\k -> 
            let qq = makeQ (qs ! k) (ls ! k)
                dik = (x ! i) `sub` (means ! k)
                mahal = sqnorm (mul qq dik)
            in (alphas ! k) + R.sum (qs ! k) - 0.5 * mahal)
    ))) - 
    (fromIntegral n) * (logsumexp alphas) +
        0.5 * R.sum (build kk (\k -> sqnorm (expv (qs ! k)) + sqnorm (ls ! k)))

-- Log of Wishart prior
log_wishart_prior :: Floating a => Int -> a -> Int -> Mat a -> Mat a -> a
log_wishart_prior p wishart_gamma wishart_m qs ls =
    let kk = size qs
        n = p + wishart_m + 1
        cc = (fromIntegral (n*p))*((log wishart_gamma) - 0.5*(log 2)) - (log_gamma_distrib (0.5*(fromIntegral n)) p)

        out = R.sum (build kk (\ik -> 
                        let frobenius1 = sqnorm (qs ! ik) -- TODO: exp?
                            frobenius2 = sqnorm (ls ! ik)
                        in 0.5*wishart_gamma*wishart_gamma*(frobenius1+frobenius2) - (fromIntegral wishart_m)*(R.sum (qs ! ik)) -- TODO: sum...
                           ))
    in out - (fromIntegral kk)*cc

-- GMM with prior
gmm_with_prior x alphas means qs ls wishart_m wishart_gamma =
    gmm_objective x alphas means qs ls + 
    log_wishart_prior (size (x ! 0)) wishart_gamma wishart_m qs ls

{- -- When we start probabilistic programming
-- Sample from GMM
let gmm_sample (rng: RNG) (alphas:Vec) (means:Vec[]) (qs:Vec[]) (ls:Vec[]) =
    let K = size alphas
    let k = categorical_sample rng alphas
    let InvSqrtSigma = makeQ qs.[k] ls.[k]
    invSqrtGaussian_sample rng Q means.[k]   
-}

data Args a = Args (Mat a) (Vec a) (Mat a) (Mat a) (Mat a) a
  deriving (Functor, Foldable, Show)

instance Traversable Args where
  traverse f (Args a1 a2 a3 a4 a5 aa) =
    Args <$> (traverse . traverse) f a1
         <*> traverse f a2
         <*> (traverse . traverse) f a3
         <*> (traverse . traverse) f a4
         <*> (traverse . traverse) f a5
         <*> f aa

example :: (Floating a, Ord a)
        => (Args a -> a, Args a)
example =
  let d = 10
      n = 500
      k = 10
      unity = 1
      small = 0.1

      x = build n (\_ -> build d (\_ -> unity))
      alphas = build k (\_ -> unity)
      mus = build k (\_ -> build d (\_ -> unity))
      qs = build k (\_ -> build d (\_ -> small))
      ls = build k (\_ -> build (tri d) (\_ -> unity))
      wishart_gamma = 3.1
      wishart_m = 7

  in (\(Args a1 a2 a3 a4 a5 aa) ->
        gmm_with_prior a1 a2 a3 a4 a5 wishart_m aa,
       Args x alphas mus qs ls wishart_gamma)
