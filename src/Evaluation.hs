{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
-- | This module implements a closure-based call-by-value evaluation.
-- It still has memory problem when generating super-large circuits.

module Evaluation (evaluation, evaluate, renameTemp, size, toVal, getAllWires) where

import Syntax
import SyntacticOperations
import Utils
import Nominal
import Simulation
import TCMonad
import TypeError


import Control.Monad.State
import Control.Monad.Identity
import Control.Monad.Except

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Set (Set)
import qualified Data.Set as Set
import Debug.Trace




-- * The evaluation functions for TCMonad.

-- | Evaluate an expression with an underlying circuit, return value and the updated circuit.
evaluate :: Morphism -> Exp -> TCMonad (Value, Morphism)
evaluate circ e =
  do st <- get
     let gl = globalCxt $ lcontext st
         (r, s) = runState (runExceptT $ eval Map.empty e)
                  ES{morph = circ, evalEnv = gl}
     case r of
       Left e -> throwError $ EvalErr e
       Right r -> return (r, morph s)

-- | Evaluate a parameter term and return a value. 
evaluation :: Exp -> TCMonad Value
evaluation e =
  do st <- get
     let gl = globalCxt $ lcontext st
         (r, _) = runState (runExceptT $ eval Map.empty e)
                  ES{morph = Morphism VStar [] VStar, evalEnv = gl}
     case r of
       Left e -> throwError $ EvalErr e
       Right r -> return r

-- * The Eval monad and eval function.

-- | The evaluation monad.
type Eval a = ExceptT EvalError (State EvalState) a

-- | Evaluator state, it contains an underlying circuit and
-- a global context. 
data EvalState =
  ES { morph :: Morphism, -- ^ The underlying incomplete circuit.
       evalEnv :: Context  -- ^ The global evaluation context.
     }

-- | Evaluate an expression to
-- a value in the value domain. The eval function also takes an environment
-- as argument and form a closure when evaluating a lambda abstraction or a lifted term.

eval :: Map Variable Value -> Exp -> Eval Value
eval lenv (Var x) =
  return $ lookupLEnv x lenv 

eval lenv Star = return VStar
eval lenv Unit = return VUnit
eval lenv a@(Const k) =
  do st <- get
     let genv = evalEnv st
     case Map.lookup k genv of
       Nothing -> throwError $ UndefinedId k
       Just e ->
         case identification e of
           DataConstr _ -> return (VConst k)
           DefinedGate v -> return v
           DefinedFunction (Just (_, v, _)) -> return v
           DefinedMethod _ v -> return v
           DefinedInstFunction _ v -> return v

eval lenv (Base k) = return $ VBase k

eval lenv a@(LBase k) =
  do st <- get
     let genv = evalEnv st
     case Map.lookup k genv of
       Nothing -> throwError $ UndefinedId k
       Just e ->
         case identification e of
           DataType Simple _ (Just (LBase id)) -> return (VLBase id)
           DataType (SemiSimple _) _ (Just d) -> eval lenv d
           DataType _ _ Nothing -> return (VBase k)

eval lenv (Force m) =
  do m' <- eval lenv m
     case m' of
       VLift (Abst lenv' e) -> eval lenv' e
       w@(VLiftCirc _) -> return w
       v@(VApp VUnBox _) -> return $ VForce v

eval lenv (Tensor e1 e2) =
  do e1' <- eval lenv e1
     e2' <- eval lenv e2
     return $ VTensor e1' e2'

eval lenv a@(LamV vs body) =
  -- return $ VLam $ abst lenv body
  do -- let (lenv', _) = Map.partitionWithKey (\ k a -> k `elem` vs) lenv
     let lenv' = subMap lenv vs
     return $ VLam $ abst lenv' body
     
eval lenv a@(LiftV vs body) = -- return $ VLift $ abst lenv body
  do -- let (lenv', _) = Map.partitionWithKey (\ k a -> k `elem` vs) lenv
     let lenv' = subMap lenv vs
     return $ VLift $ abst lenv' body
     
eval lenv UnBox = return VUnBox
eval lenv Revert = return VRevert
eval lenv a@(Box) = return VBox
eval lenv a@(ExBox) = return VExBox
eval lenv RunCirc = return VRunCirc

eval lenv (App m n) =
  do v <- eval lenv m
     w <- eval lenv n
     evalApp v w

eval lenv (Pair m n) = 
  do v <- eval lenv m
     w <- eval lenv n
     return (VPair v w)

eval lenv (Let m bd) =
  do m' <- eval lenv m
     open bd $ \ x n ->
        let lenv' = Map.insert x m' lenv
        in eval lenv' n


eval lenv (LetPair m (Abst xs n)) =
  do m' <- eval lenv m
     let r = unVPair (length xs) m'
     case r of
       Just vs -> do
         let lenv' = foldl (\ a (x, y) -> Map.insert x y a)
                       lenv (zip xs vs)
         eval lenv' n
       Nothing -> throwError $ TupleMismatch xs m'


eval lenv (LetPat m bd) =
  do m' <- eval lenv m
     case vflatten m' of
       Nothing -> error ("from LetPat" ++ (show $ disp m'))
       Just (Left id, args) ->
         open bd $ \ p m ->
         case p of
           PApp kid vs
             | kid == id ->
               do let vs' = map (\ (Right x) -> x) vs
                      subs = (zip vs' args)
                      lenv' = foldl (\ y (x, v) -> Map.insert x v y) lenv subs
                  eval lenv' m
           p -> throwError $ PatternMismatch p m'

eval lenv b@(Case m (B bd)) =
  do m' <- eval lenv m
     case vflatten m' of
       Nothing -> error ("from eval (Case):" ++ (show $ disp b))
       Just (Left id, args) ->
         reduce id args bd
  where reduce id args (bd:bds) =
          open bd $ \ p m ->
          case p of
             PApp kid vs
               | kid == id -> 
               do st <- get
                  let vs' = map (\ (Right x) -> x) vs
                      subs = zip vs' args
                      lenv' = foldl (\ y (x, v) -> Map.insert x v y) lenv subs
                  eval lenv' m
               | otherwise -> reduce id args bds
        reduce id args [] = throwError $ MissBranch id b

eval lenv a@(Pos _ e) = error "position in eval"
eval lenv a = error $ "from eval: " ++ (show $ disp a)

-- * Helper functions for eval.

-- | Look up a value from the local environment.
lookupLEnv ::  Variable -> Map Variable Value -> Value
lookupLEnv x lenv =
  case Map.lookup x lenv of
    Nothing -> error "from lookupLEnv"
    Just v -> v

-- | A helper function for evaluating various of applications.
evalApp :: Value -> Value -> Eval Value

evalApp VUnBox v | Wired _ <- v = return $ VApp VUnBox v
evalApp VUnBox v | otherwise = return VUnBox
evalApp (VForce (VApp VUnBox v)) w =
  case v of
    Wired bd ->
      open bd $ \ wires m ->
      case m of
        f@(VCircuit (Morphism ins gs outs)) ->
          let binding = makeBinding ins w 
          in appendMorph binding (Morphism ins gs outs)
    a -> error $ "evalApp(Unbox ..) " ++ (show $ disp a)

evalApp (VApp (VApp (VApp VBox q) _) _) v =
  case v of
    VLift (Abst lenv' m) ->
      evalBox lenv' m q
    VApp VUnBox w -> return w

evalApp (VApp (VApp (VApp (VApp VExBox q) _) _) _) v =  
  case v of
    VLift (Abst lenv body) ->
      evalExbox lenv body q

evalApp (VApp (VApp (VApp VRunCirc  _) _) (Wired (Abst _ (VCircuit m)))) input =
  case runCircuit m input of
    Left e -> throwError $ SimulationErr e
    Right r -> return r


evalApp (VApp (VApp VRevert _) _) m' =
  case m' of
    Wired bd ->
      open bd $ \ ws (VCircuit (Morphism ins gs outs)) ->
      let gs' = revGates gs in
        return $ Wired (abst ws (VCircuit $ Morphism outs gs' ins))

evalApp a@(Wired _) w = return a

evalApp v w = 
  let (h, res) = unwindVal v
  in case h of
    VLam (Abst lenv bd) -> handleBody lenv res bd
    VLiftCirc (Abst vs (Abst lenv e)) -> 
        do let args = res ++ [w]
               lvs = length vs
           if lvs > (length args) then
             return $ VApp v w
             else do let sub = zip vs args
                         ws = drop lvs args
                         lenv' = updateCirc sub lenv
                         lenv'' = lenv' `Map.union` Map.fromList sub
                     e' <- eval lenv'' e
                     return $ foldl VApp e' ws
        
    _ -> return $ VApp v w
          
  where unwindVal (VApp t1 t2) =
          let (h, args) = unwindVal t1
          in (h, args++[t2])
        unwindVal a = (a, [])
        -- Handle beta reduction
        handleBody lenv res bd = open bd $ \ vs m ->
             let args = res ++ [w]
                 lvs = length vs
             in
              if lvs > length args
              then return $ VApp v w
              else do let sub = zip vs args
                          ws = drop lvs args
                          lenv' = foldr (\ (x,v) y -> Map.insert x v y) lenv sub
                      m' <- eval lenv' m
                      return $ foldl VApp m' ws
        -- Perform substitution on the variables in a circuit.
        updateCirc sub lenv =
             let (x, circ):[] = Map.toList lenv
                 Wired (Abst wires (VCircuit (Morphism ins
                                               [Gate id params gin gout ctrls] outs)))
                   = circ
                 params' = helper params sub
                 ctrls':[] = helper [ctrls] sub
                 circ' = Wired (abst wires
                                 (VCircuit (Morphism ins
                                             [Gate id params' gin gout ctrls'] outs)))
             in Map.fromList [(x, circ')]
        -- Perfrom substitution.             
        helper :: [Value] -> [(Variable, Value)] -> [Value]
        helper [] lc = []
        helper (VStar:xs) lc = VStar:helper xs lc
        helper ((VVar x):xs) lc =
             let res = helper xs lc in
             case lookup x lc of
               Just v -> v:res
               Nothing -> error $ "can't find variable " ++ (show $ disp x)

-- | Evaluate a box term.
evalBox :: LEnv -> Exp -> Value -> Eval Value               
evalBox lenv body uv =
  freshLabels (genNames uv) $ \ vs ->
   do st <- get
      b <- eval lenv body
      let uv' = toVal uv vs
          d = Morphism uv' [] uv'
          (res, st') = runState (runExceptT $ evalApp b uv') st{morph = d}
      case res of
        Left e -> throwError e
        Right res' -> 
          let Morphism ins gs _ = morph st'
              newMorph = Morphism ins (reverse gs) res'
              wires = getAllWires newMorph
              morph' = Wired $ abst wires (VCircuit newMorph)
          in return morph'

-- | Evaluate an existsBox term. Note that
-- it is tempting to combine 'evalExbox' and 'evalBox' into one function,
-- but this will introduce bug, because we do not distinguish existential
-- pair and the usual tensor pair at runtime, the evaluator may confuse
-- the tensor pair with existential pair, thus making the wrong decision.
-- So we define 'evalExbox' and 'evalBox' separately to enforce the assumptions.
evalExbox :: LEnv -> Exp -> Value -> Eval Value        
evalExbox lenv body uv =
  freshLabels (genNames uv) $ \ vs ->
   do st <- get
      b <- eval lenv body
      let uv' = toVal uv vs
          d = Morphism uv' [] uv'
          (res, st') = runState (runExceptT $ evalApp b uv') st{morph = d}
      case res of
        Left e -> throwError e
        Right (VPair n res') -> 
          let Morphism ins gs _ = morph st'
              newMorph = Morphism ins (reverse gs) res'
              wires = getAllWires newMorph
              morph' = Wired $ abst wires (VCircuit newMorph)
          in return (VPair n morph')        
        Right a -> error $ "from eval_exBox\n" ++ (show $ disp a)



-- | Append a circuit to the underline circuit state according to a binding.
-- For efficiency reason we try prepend instead of append, so 'evalBox' and 'evalExbox'
-- have to reverse the list of gates as part of the post-processing. 
appendMorph :: Binding -> Morphism -> Eval Value
appendMorph binding f@(Morphism fins fs fouts) =
  do st <- get
     let circ = morph st
         (Morphism fins' fs' fouts') = rename f binding
     case circ of
       Morphism ins gs outs ->
         let
           newCirc = Morphism ins (reverse fs'++gs) fouts' in
         do put st{morph = newCirc }
            return fouts'


-- | A binding is a map of labels. 
type Binding = Map Label Label

-- | Obtain a binding from two simple terms. 
makeBinding :: Value -> Value -> Binding
makeBinding w v =
  let ws = getWires w
      vs = getWires v
  in if length ws /= length vs
     then 
       error ("binding mismatch!\n" ++ (show $ disp w) ++
               "\n" ++ (show $ disp v))
       else Map.fromList (zip ws vs)

-- | Rename the labels of a morphism according to a binding.
rename :: Morphism -> Map Label Label -> Morphism            
rename (Morphism ins gs outs) m =
  let ins' = renameTemp ins m
      outs' = renameTemp outs m
      gs' = renameGs gs m
  in Morphism ins' gs' outs'

-- | Rename a template value according to a binding.
renameTemp :: Value -> Map Label Label -> Value
renameTemp (VLabel x) m =
  case Map.lookup x m of
    Nothing -> (VLabel x)
    Just y -> VLabel y
renameTemp a@(VConst _) m = a
renameTemp VStar m = VStar
renameTemp (VApp e1 e2) m = VApp (renameTemp e1 m) (renameTemp e2 m)
renameTemp (VPair e1 e2) m = VPair (renameTemp e1 m) (renameTemp e2 m)
renameTemp a m = error "applying renameTemp function to an ill-formed template"     

-- | Rename a list of gates according to a binding.
renameGs :: [Gate] -> Map Label Label -> [Gate]
renameGs gs m = map helper gs
  where helper (Gate id params ins outs ctrls) =
          Gate id params (renameTemp ins m) (renameTemp outs m) (renameTemp ctrls m)

   
-- | Reverse a list of gate in theory, in reality it only
-- changes the name of a gate to its adjoint, the gates are
-- already stored in reverse order due to the way we implement 'appendMorph'.
revGates :: [Gate] -> [Gate]
revGates xs = revGatesh xs [] 
  where revGatesh [] gs = gs
        revGatesh ((Gate id params ins outs ctrls):res) gs =
          let id' = invertName id
          in revGatesh res ((Gate id' params outs ins ctrls):gs)

-- | Change the name of a gate to its adjoint
invertName :: Id -> Id             
invertName id | getName id == "Init0" =  Id "Term0"
invertName id | getName id == "Init1" =  Id "Term1"
invertName id | getName id == "Term1" =  Id "Init1"
invertName id | getName id == "Term0" =  Id "Init0"
invertName id | getName id == "H" =  Id "H"
invertName id | getName id == "CNot" =  Id "CNot"
invertName id | getName id == "Not_g" =  Id "Not_g"
invertName id | getName id == "C_Not" =  Id "C_Not"
invertName id | getName id == "QNot" =  Id "QNot"
invertName id | getName id == "CNotGate" =  Id "CNotGate"
invertName id | getName id == "ToffoliGate_10" =  Id "ToffoliGate_10"
invertName id | getName id == "ToffoliGate_01" =  Id "ToffoliGate_01"
invertName id | getName id == "ToffoliGate" =  Id "ToffoliGate"
invertName id | getName id == "Mea" = error "cannot invert Mea gate"
invertName id | getName id == "Discard" = error "cannot invert Discard gate"
invertName id =  Id $ getName id ++ "*"


-- | Generate a list of wirenames from a simple data type.
genNames :: Value -> [String]
genNames uv =
  let n = size uv
      ls = "l":ls
      names = take n ls
  in names

-- | Rename uv using fresh labels draw from vs
toVal :: Value -> [Label] -> Value
toVal uv vs = evalState (templateToVal uv) vs

-- | Obtain a fresh template inhabitant of a simple type, with wirenames
-- draw from the state. The input is a simple data type
templateToVal :: Value -> State [Label] Value
templateToVal (VLBase _) =
  do x <- get
     let (v:vs) = x
     put vs
     return (VLabel v)
templateToVal a@(VConst _) = return a
templateToVal a@(VUnit) = return VStar
templateToVal (VApp e1 e2) =
  do e1' <- templateToVal e1
     e2' <- templateToVal e2
     return $ VApp e1' e2'

templateToVal (VTensor e1 e2) =
  do e1' <- templateToVal e1
     e2' <- templateToVal e2
     return $ VPair e1' e2'

templateToVal a = error "applying templateToVal function to an ill-formed template"

-- | Get the size of a simple data type.
size :: Num a => Value -> a
size (VLBase x) = 1
size (VConst _) = 0
size VUnit = 0
size (VApp e1 e2) = size e1 + size e2
size (VTensor e1 e2) = size e1 + size e2
size a = error $ "applying size function to an ill-formed template:" ++ (show $ disp a)     

-- | Obtain all the labels from the circuit.
getAllWires :: Morphism -> [Label]
getAllWires (Morphism ins gs outs) =
  let inWires = Set.fromList $ getWires ins
      outWires = Set.fromList $ getWires outs
      gsWires = Set.unions $ map getGateWires gs
  in Set.toList (inWires `Set.union` outWires `Set.union` gsWires)
  where getGateWires (Gate _ _ ins outs ctrls) =
          Set.fromList (getWires ins) `Set.union`
          Set.fromList (getWires outs) `Set.union`
          Set.fromList (getWires ctrls)

-- | Obtain a submap from a map.
subMap m vs =
  let m' = map (\ k -> case Map.lookup k m of
                         Just v -> (k, v)
                         Nothing -> error $ "from subMap, can't find:" ++ show k
               ) vs
      m'' = Map.fromList m'
  in m''
