{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}

import qualified Data.Map                      as M
import qualified Streaming                     as S
import qualified Streaming.Prelude             as S
import qualified Control.Monad.State           as St

data Value = FloatV Float | TupleV [Value] deriving Show

data Function = Mul | Sub | Div | SqR deriving Show

data Cmd = Call Var Function Var
         | Tuple Var [Var]
         | Untuple [Var] Var
         | Dup (Var, Var) Var
         | Add Var (Var, Var)
         | Lit Var Value
         | Elim Var
         deriving Show

type Prog = [Cmd]

type Var = String

type Env = M.Map Var Value

call :: Function -> Value -> Maybe Value
call Mul (TupleV [FloatV x1, FloatV x2]) = Just (FloatV (x1 * x2))
call Sub (TupleV [FloatV x1, FloatV x2]) = Just (FloatV (x1 - x2))
call Div (TupleV [FloatV x1, FloatV x2]) = Just (FloatV (x1 / x2))
call SqR (TupleV [FloatV x1, FloatV x2]) = Just (FloatV (-x1 / (x2 * x2)))
call _   _                               = Nothing

-- Could do this directly with `WriterT a Maybe` I think.
-- A good example for typeclass dictionaries?
pop :: Ord k => k -> M.Map k v -> Maybe (v, M.Map k v)
pop k m = do
  let (mv, m') = M.alterF (\u -> (u, Nothing)) k m
  v <- mv
  pure (v, m')

note :: String -> Maybe a -> Either String a
note s = \case
  Nothing -> Left s
  Just a  -> pure a

eval :: Env -> Prog -> Either String Env
eval env []       = pure env
eval env (c : cs) = do
  env' <- env'E
  eval env' cs
 where
  env'E = case c of
    Call v' f vv -> do
      (t, envWithoutv) <-
        note ("Could not pop " ++ show vv ++ " when calling") $ pop vv env
      vvv <- note ("Could not call " ++ show f) $ call f t
      pure (M.insert v' vvv envWithoutv)
    Tuple v' vs -> do
      let
        newVars = forWithState (S.each vs) env $ \(vv, env_) -> do
          (t, envWithoutV) <-
            S.lift
              ( note ("Could not pop " ++ show vv ++ " when tupling")
              $ pop vv env_
              )
          S.yield t
          pure envWithoutV

      (ts S.:> ((), envFinal)) <- S.toList newVars

      pure (M.insert v' (TupleV ts) envFinal)
    Untuple vs v -> do
      (tuplet, envWithoutV) <-
        note ("Could not pop " ++ show v ++ " when Untupling") $ pop v env

      t <- case tuplet of
        TupleV t -> pure t
        other    -> Left ("Tuple " ++ show v ++ " was " ++ show other)

      -- Zip doesn't check for equal length
      let inserts = forWithState (S.each (zip t vs)) envWithoutV
            $ \((tv, vv), env_) -> pure (M.insert vv tv env_)

      (_ S.:> ((), envFinal)) <- S.toList inserts

      pure envFinal

    Dup (v1, v2) v -> do
      (t, envWithoutV) <-
        note ("Could not pop " ++ show v ++ " when duping") $ pop v env
      let insertNew = M.insert v1 t . M.insert v2 t
      pure (insertNew envWithoutV)
    Lit v value    -> pure (M.insert v value env)
    Add v (v1, v2) -> do
      (FloatV t1, env1) <- note ("Add: " ++ show v1) $ pop v1 env
      (FloatV t2, env2) <- note ("Add: " ++ show v2) $ pop v2 env1
      pure (M.insert v (FloatV (t1 + t2)) env2)
    Elim v -> do
      (_, envWithoutV) <-
        note ("Could not pop " ++ show v ++ " when Eliming") $ pop v env
      pure envWithoutV


vf, vr :: Var -> Var
vf = (++ "")
vr = (++ "r")

rev :: Prog -> (Prog, [Var], [Var] -> Prog)
rev []       = ([], [], const [])
rev (c : cs) = let (pf, xs, pr) = rev cs in case c of
  Add v (v1, v2) ->
    ( Add (vf v) (vf v1, vf v2) : pf
    , xs
    , \xs' -> pr xs' ++ [Dup (vr v1, vr v2) (vr v)]
    )
  Call v f vv -> case f of
    Sub -> error "Sub"
    Mul ->
      ( Dup (vv ++ "1", vv ++ "2") vv
        : Untuple [vv ++ "at1", vv ++ "at2"] (vv ++ "1")
        : Call v Mul (vv ++ "2")
        : pf
      , (vv ++ "at1") : (vv ++ "at2") : xs
      , \(v12 : v22 : xs') ->
        pr xs'
          ++ [ Dup (vr v ++ "1", vr v ++ "2") (vr v)
             , Tuple (vv ++ "t1") [vr v ++ "1", v12]
             , Tuple (vv ++ "t2") [vr v ++ "2", v22]
             , Call (vv ++ "t1m") Mul (vv ++ "t1")
             , Call (vv ++ "t2m") Mul (vv ++ "t2")
             , Tuple (vr vv) [vv ++ "t2m", vv ++ "t1m"]
             ]
      )
    Div ->
      ( Dup (vv ++ "1", vv ++ "2") vv
        : Untuple [vv ++ "at1", vv ++ "at2"] (vv ++ "1")
        : Call v Div (vv ++ "2")
        : pf
      , (vv ++ "at1") : (vv ++ "at2") : xs
      , \(v12 : v22 : xs') ->
        pr xs'
          ++ [ Dup (vr v ++ "1", vr v ++ "2") (vr v)
             , Tuple (vv ++ "t1") [vr v ++ "1", v12]
             , Tuple (vv ++ "t2") [vr v ++ "2", v22]
             , Call (vv ++ "t1m") Div (vv ++ "t1")
             , Call (vv ++ "t2m") SqR (vv ++ "t2")
             , Tuple (vr vv) [vv ++ "t1m", vv ++ "t2m"]
             ]
      )
    SqR -> undefined
  Tuple t vs ->
    ( Tuple (vf t) (map vf vs) : pf
    , xs
    , \xs' -> pr xs' ++ [Untuple (map vr vs) (vr t)]
    )
  Untuple{} -> error "Untuple"
  Dup (v1, v2) v ->
    ( Dup (vf v1, vf v2) (vf v) : pf
    , xs
    , \xs' -> pr xs' ++ [Add (vr v) (vr v1, vr v2)]
    )
  Lit v lit -> (Lit (vf v) lit : pf, xs, \xs' -> pr xs' ++ [Elim (vr v)])
  Elim{} -> error "Elim"

rev2 :: Prog -> Prog
rev2 p = pf ++ pr vs where (pf, vs, pr) = rev p

example :: Prog
example = [Add "z" ("x", "y"), Dup ("z1", "z2") "z"]

awf :: Prog
awf =
  [ Lit "7" (FloatV 7)
  , Dup ("x1", "x2") "x"
  , Tuple "7x" ["7", "x1"]
  , Call "p" Mul "7x"
  , Dup ("p1", "p2") "p"
  , Lit "1" (FloatV 1)
  , Tuple "1/y" ["1", "y"]
  , Call "r" Div "1/y"
  , Tuple "px" ["p1", "x2"]
  , Call "p*x" Mul "px"
  , Lit "5" (FloatV 5)
  , Tuple "p*x5" ["p*x", "5"]
  , Call "q" Mul "p*x5"
  , Lit "2" (FloatV 2)
  , Tuple "2p" ["2", "p2"]
  , Call "2*p" Mul "2p"
  , Tuple "2*p_q" ["2*p", "q"]
  , Call "2*p*q" Mul "2*p_q"
  , Lit "3" (FloatV 3)
  , Tuple "3_r" ["3", "r"]
  , Call "3*r" Mul "3_r"
  , Add "v" ("2*p*q", "3*r")
  ]

awff :: Fractional a => a -> a -> a
awff x y =
  let p = 7 * x
      r = 1 / y
      q = p * x * 5
      v = 2 * p * q + 3 * r
  in  v

awff_rev :: Fractional a => a -> a -> a -> (a, a)
awff_rev x y dα_dv =
  let p     = 7 * x
      q     = p * x * 5

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

test :: IO ()
test = do
  print (eval (M.fromList [("x", FloatV 3), ("y", FloatV 4)]) example)
  print (rev2 example)
  print (eval (M.fromList [("x", FloatV 3), ("y", FloatV 4)]) awf)
  print (awff (3.0 :: Double) 4.0)

  print
    (eval (M.fromList [("x", FloatV 3), ("y", FloatV 4), ("vr", FloatV 1)])
          (rev2 awf)
    )
  print (awff_rev (3.0 :: Double) 4.0 1.0)

sexample :: Monad m => S.Stream (S.Of Integer) m ((), String)
sexample = forWithState (S.each [1 .. 10]) "" $ \(i, s) -> do
  S.yield i
  pure (s ++ show i ++ ",")

forWithState
  :: forall a f s m r
   . (Monad m, Functor f)
  => S.Stream (S.Of a) m r
  -> s
  -> ((a, s) -> S.Stream f m s)
  -> S.Stream f m (r, s)
forWithState stream initialState f = St.runStateT (switch inStateT)
                                                  initialState
 where
  inStateT :: S.Stream f (St.StateT s m) r
  inStateT = S.for (S.hoist S.lift stream) $ \a -> do
    s  <- St.lift St.get
    s' <- S.hoist S.lift (f (a, s))
    St.lift (St.put s')

switch
  :: ( Functor f
     , Monad m
     , Monad (t m)
     , St.MonadTrans t
     , Monad (t (S.Stream f m))
     , S.MFunctor t
     )
  => S.Stream f (t m) a
  -> t (S.Stream f m) a
switch s = S.destroy s yieldsT effectT pure

yieldsT
  :: (Functor f, Monad m, St.MonadTrans t, Monad (t (S.Stream f m)))
  => f (t (S.Stream f m) a)
  -> t (S.Stream f m) a
yieldsT = St.join . S.lift . S.yields

effectT
  :: (Monad (t (streamf m)), Monad m, St.MonadTrans streamf, S.MFunctor t)
  => t m (t (streamf m) a)
  -> t (streamf m) a
effectT = St.join . S.hoist S.lift
