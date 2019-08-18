{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}

import qualified Data.Map                      as M
import qualified Streaming                     as S
import qualified Streaming.Prelude             as S
import qualified Data.Sequence                 as Seq
import qualified Control.Monad.State           as St
import qualified Control.Lens                  as L

data Value = FloatV Float
           | IntV Int
           | TupleV [Value]
           | VectorV (Seq.Seq Value)
           | UnitV
  deriving Show

data Function = Mul
              | Sub
              | Div
              | SqR
              | Index
              | IncAt
              | StoreAt
              | ToFloat
              | NewVec
              deriving Show

data Cmd = Call Var Function Var
         | Tuple Var [Var]
         | Untuple [Var] Var
         | Dup (Var, Var) Var
         | Add Var (Var, Var)
         | Lit Var Value
         | Elim Var
         | ForRange Var Var (Var, Var) Prog Var Var
         | ForRangeRev Var Var (Var, Var) Prog Var Var
         deriving Show

type Prog = [Cmd]

type Var = String

type Env = M.Map Var Value

call :: Function -> Value -> Maybe Value
call Mul (TupleV [FloatV x1, FloatV x2]) = Just (FloatV (x1 * x2))
call Sub (TupleV [FloatV x1, FloatV x2]) = Just (FloatV (x1 - x2))
call Div (TupleV [FloatV x1, FloatV x2]) = Just (FloatV (x1 / x2))
call SqR (TupleV [FloatV x1, FloatV x2, FloatV x3]) =
  Just (FloatV (-(x1 * x3) / (x2 * x2)))
call Index (TupleV [VectorV v, IntV i]) =
  Just (TupleV [VectorV v, Seq.index v i])
call IncAt (TupleV [VectorV v, IntV i, FloatV a]) = do
  v' <- L.traverseOf
    (L.ix i)
    (\case
      FloatV v_i -> Just (FloatV (v_i + a))
      _          -> Nothing
    )
    v
  pure (VectorV v')
call ToFloat (IntV i) = Just (FloatV (fromIntegral i))
call StoreAt (TupleV [VectorV v, IntV i, a]) =
  Just (VectorV (L.set (L.ix i) a v))
call NewVec (IntV n) = Just (VectorV (Seq.replicate n dummyValue))
  where -- We can only fill in with a dummy value at the moment
        -- because we don't know what type to fill in with.
        -- I guess we'll fix this later.
        dummyValue = UnitV
call _ _ = Nothing

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
      vvv <- note ("Could not call " ++ show f ++ " with arg " ++ show t)
        $ call f t
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
    ForRange nV sV (iPV, sPV) prog s'PV s'V ->
      evalForRange env (\n -> [0..n-1]) nV sV (iPV, sPV) prog s'PV s'V
    ForRangeRev nV sV (iPV, sPV) prog s'PV s'V ->
      evalForRange env (\n -> [n-1,n-2..0]) nV sV (iPV, sPV) prog s'PV s'V

evalForRange :: Env
             -> (Int -> [Int])
             -> Var
             -> Var
             -> (Var, Var)
             -> Prog
             -> [Char]
             -> Var
             -> Either String (M.Map Var Value)
evalForRange env range nV sV (iPV, sPV) prog s'PV s'V = do
      (IntV n, envWithoutN) <- note ("Pop in ForRange: " ++ show nV)
        $ pop nV env
      (s, envWithoutNS) <- note ("Pop in ForRange: " ++ show sV)
        $ pop sV envWithoutN
      let runRange =
            forWithState (S.each (range n)) (envWithoutNS, s)
              $ \(i, (env_, s_)) -> do
                  let env_i_s = (M.insert iPV (IntV i) . M.insert sPV s_) env_
                  env'               <- S.lift (eval env_i_s prog)
                  (s', envWithoutS') <- S.lift
                    (note ("Pop in ForRange: " ++ s'PV) $ pop s'PV env')
                  pure (envWithoutS', s')

      (_ S.:> ((), (envRange, sFinal))) <- S.toList runRange
      pure (M.insert s'V sFinal envRange)


vf, vr :: Var -> Var
vf = (++ "")
vr = (++ "r")

rev :: Prog -> (Prog, [Var], [Var] -> Prog)
rev [] = ([], [], const [])
rev (c : cs) =
  let (pf, xs, pr) = rev cs
      ff (a, b, cc) = (a ++ pf, b ++ xs, cc)
  in  case c of
        Add v (v1, v2) -> ff
          ( [Add (vf v) (vf v1, vf v2)]
          , []
          , \xs' -> pr xs' ++ [Dup (vr v1, vr v2) (vr v)]
          )
        Call v f vv -> case f of
          Sub -> error "Sub"
          Mul -> ff
            ( [ Dup (vv ++ "1", vv ++ "2") vv
              , Untuple [vv ++ "at1", vv ++ "at2"] (vv ++ "1")
              , Call v Mul (vv ++ "2")
              ]
            , [vv ++ "at1", vv ++ "at2"]
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
          Div -> ff
            ( [ Dup (vv ++ "1", vv ++ "2") vv
              , Untuple [vv ++ "at1", vv ++ "at2"] (vv ++ "1")
              , Call v Div (vv ++ "2")
              ]
            , [vv ++ "at1", vv ++ "at2"]
            , \(v12 : v22 : xs') ->
              pr xs'
                ++ [ Dup (vr v ++ "1", vr v ++ "2") (vr v)
                   , Dup (v22 ++ "1" , v22 ++ "2")  v22
                   , Tuple (vv ++ "t1") [vr v ++ "1", v22 ++ "1"]
                   , Tuple (vv ++ "t2") [v12, v22 ++ "2", vr v ++ "2"]
                   , Call (vv ++ "t1m") Div (vv ++ "t1")
                   , Call (vv ++ "t2m") SqR (vv ++ "t2")
                   , Tuple (vr vv) [vv ++ "t1m", vv ++ "t2m"]
                   ]
            )
          SqR   -> undefined
          Index -> ff
            ( [ Untuple [vv ++ "$v", vv ++ "$i"] vv
              , Dup (vv ++ "$i1", vv ++ "$i2") (vv ++ "$i")
              , Tuple (vv ++ "$'") [vv ++ "$v", vv ++ "$i1"]
              , Call v Index (vv ++ "$'")
              ]
            , [vv ++ "$i2"]
            , \(i : xs') ->
              pr xs'
                ++ [ Untuple [v ++ "$v", v ++ "$a"] (vr v)
                   , Tuple (v ++ "$v_i_a") [v ++ "$v", i, v ++ "$a"]
                   , Call (vr vv ++ "$vector") IncAt (v ++ "$v_i_a")
                   , Lit (vv ++ "$old_index") UnitV
                   , Tuple (vr vv) [vr vv ++ "$vector", vv ++ "$old_index"]
                   ]
            )
          IncAt   -> error "rev of IncAt"
          ToFloat -> error "ToFloat"
          NewVec  -> error "NewVec"
          StoreAt -> error "StoreAt"
        Tuple t vs -> ff
          ( [Tuple (vf t) (map vf vs)]
          , []
          , \xs' -> pr xs' ++ [Untuple (map vr vs) (vr t)]
          )
        Untuple vs t -> ff
          ( [Untuple (map vf vs) (vf t)]
          , []
          , \xs' -> pr xs' ++ [Tuple (vr t) (map vr vs)]
          )
        Dup (v1, v2) v -> ff
          ( [Dup (vf v1, vf v2) (vf v)]
          , []
          , \xs' -> pr xs' ++ [Add (vr v) (vr v1, vr v2)]
          )
        Lit v lit -> ff ([Lit (vf v) lit], [], \xs' -> pr xs' ++ [Elim (vr v)])
        Elim{}    -> error "Elim"
        ForRange nV sV (iPV, sPV) prog s'PV s'V ->
          let
            (progf, progtrace, progr) = rev prog
            progfstoretrace =
              [ Untuple [sPV, nV ++ "$P_looptrace"] (nV ++ "$P_s_looptrace")
                -- Duplicating and keeping the same name is not ideal
                -- but we may get away with it.
                , Dup (iPV, iPV ++ "$2") iPV
                ]
                ++ progf
                ++ [ Tuple (nV ++ "$progtrace") progtrace
                   , Tuple
                     (nV ++ "$v_i_a")
                     [nV ++ "$P_looptrace", iPV ++ "$2", nV ++ "$progtrace"]
                   , Call (nV ++ "$P_looptrace'") StoreAt (nV ++ "$v_i_a")
                   , Tuple (nV ++ "$P_s_looptrace'")
                           [s'PV, nV ++ "$P_looptrace'"]
                   ]
            progrstoretrace =
              [ Dup (vr iPV, vr iPV ++ "$2") (vr iPV)
              , Untuple [vr s'PV, vr nV ++ "$P_looptrace'"]
                        (vr nV ++ "$P_s_looptrace'")
              , Tuple (vr nV ++ "$P_looptrace'_i")
                      [vr nV ++ "$P_looptrace'", vr iPV ++ "$2"]
              , Call (vr nV ++ "$v_i") Index (vr nV ++ "$P_looptrace'_i")
              , Untuple [vr nV ++ "$P_looptrace", vr nV ++ "$progtrace"]
                        (vr nV ++ "$v_i")
              , Untuple (map vr progtrace) (vr nV ++ "$progtrace")
              ]
              ++ progr (map vr progtrace)
              ++ [ Tuple (vr nV ++ "$P_s_looptrace")
                         [vr sPV, vr nV ++ "$P_looptrace"]
                 ]
          in
            ff
              ( [ Dup (nV ++ "$again", nV ++ "$1") nV
                , Dup (nV ++ "$2"    , nV ++ "$3") (nV ++ "$again")
                , Call (nV ++ "$looptrace") NewVec (nV ++ "$1")
                , Tuple (nV ++ "$s_looptrace") [sV, nV ++ "$looptrace"]
                , ForRange (nV ++ "$2")
                           (nV ++ "$s_looptrace")
                           (iPV, nV ++ "$P_s_looptrace")
                           progfstoretrace
                           (nV ++ "$P_s_looptrace'")
                           (nV ++ "$s_looptrace'")
                , Untuple [s'V, nV ++ "$looptrace'"] (nV ++ "$s_looptrace'")
                ]
              , [nV ++ "$3", nV ++ "$looptrace'"]
              , \(nV2 : nVs_looptrace' : xs') ->
                pr xs'
                  ++ [Tuple (vr nV ++ "$s_looptrace'") [vr s'V, nVs_looptrace']
                     , ForRangeRev nV2
                                   (vr nV ++ "$s_looptrace'")
                                   (vr iPV, vr nV ++ "$P_s_looptrace'")
                                   progrstoretrace
                                   (vr nV ++ "$P_s_looptrace")
                                   (vr nV ++ "$s_looptrace")
                     , Untuple [vr sV, vr nV ++ "$looptrace"]
                               (vr nV ++ "$s_looptrace")
                     , Elim (vr nV ++ "$looptrace")
                     ]
              )
        ForRangeRev{} -> error "ForRangeRev"

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
  , Lit "11" (FloatV 11)
  , Tuple "11/y" ["11", "y"]
  , Call "r" Div "11/y"
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

indexexample :: Prog
indexexample =
  [ Lit "3" (IntV 3)
  , Tuple "t" ["v", "3"]
  , Call "v_v_3" Index "t"
  , Untuple ["v'", "v_3"] "v_v_3"
  ]

indexincexample :: Prog
indexincexample =
  indexexample
    ++ [ Lit "5"    (IntV 5)
       , Lit "1000" (FloatV 1000)
       , Tuple "v'_5_1000" ["v'", "5", "1000"]
       , Call "v''" IncAt "v'_5_1000"
       ]

triangleexample :: Prog
triangleexample = [ForRange "n" "acc_in" ("i", "acc") loop "acc'" "acc_res"]
  where loop = [Call "i_f" ToFloat "i", Add "acc'" ("i_f", "acc")]

sumexample :: Prog
sumexample =
  [ Lit "acc_in" (FloatV 0)
  , Tuple "v_acc_in" ["v_in", "acc_in"]
  , ForRange "n" "v_acc_in" ("i", "v_acc") loop "v_acc'" "v_acc_res"
  ]
 where
  loop =
    [ Untuple ["v", "acc"] "v_acc"
    , Tuple "v_i" ["v", "i"]
    , Call "v'_vi" Index "v_i"
    , Untuple ["v'", "vi"] "v'_vi"
    , Add "acc'" ("acc", "vi")
    , Tuple "v_acc'" ["v'", "acc'"]
    ]

awff :: Fractional a => a -> a -> a
awff x y =
  let p = 7 * x
      r = 11 / y
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
      dr_dy = -11 / (y * y)

      dq_dx = p * 5
      dq_dy = 0

      dp_dx = 7
      dp_dy = 0

      dα_dx = dα_dp * dp_dx + dα_dq * dq_dx + dα_dr * dr_dx + dα_dv * dv_dx
      dα_dy = dα_dp * dp_dy + dα_dq * dq_dy + dα_dr * dr_dy + dα_dv * dv_dy
  in  (dα_dx, dα_dy)

printExample :: [(Var, Value)] -> Prog -> IO ()
printExample bindings = print . eval (M.fromList bindings)

test :: IO ()
test = do
  printExample [("x", FloatV 3), ("y", FloatV 4)] example
  print (rev2 example)
  printExample [("x", FloatV 3), ("y", FloatV 4)] awf
  print (awff (3.0 :: Double) 4.0)

  let range10 = VectorV (Seq.fromList (map (FloatV . (* 10)) [0 .. 9]))

  putStrLn "Index example"
  printExample [("v", range10)] indexexample
  printExample [("v", range10)] indexincexample
  printExample
    [ ("v'r" , VectorV (Seq.replicate 10 (FloatV 0)))
    , ("v_3r", FloatV 11)
    , ("v"   , range10)
    ]
    (rev2 indexexample)

  printExample [("x", FloatV 3), ("y", FloatV 4), ("vr", FloatV 1)] (rev2 awf)
  print (awff_rev (3.0 :: Double) 4.0 1.0)

  printExample [("n", IntV 10), ("acc_in", FloatV 0)] triangleexample
  printExample [("n", IntV 10), ("v_in", range10)]    sumexample
  printExample
    [ ("n", IntV 10)
    , ("v_in", range10)
    , ("v_acc_resr", TupleV [VectorV (Seq.replicate 10 (FloatV 100)), FloatV 66])
    ]
    (rev2 sumexample)

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
