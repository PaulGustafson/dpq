{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE BangPatterns #-}
-- | This module implements a closure-based call-by-value evaluation.
-- It still has memory problem when generating super-large circuits.

module Evaluation (evaluation, evaluate, renameTemp, size, toVal, getAllWires) where

import Syntax
import Erasure
import SyntacticOperations
import Utils
import Nominal
import Simulation
import TCMonad
import TypeError


import Control.Monad.State.Strict
import Control.Monad.Identity
import Control.Monad.Except

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Set (Set)
import Data.List
import qualified Data.Set as S
import Debug.Trace




-- * The evaluation functions for TCMonad.

-- | Evaluate an expression with an underlying circuit, return value and the updated circuit.
evaluate :: Morphism -> EExp -> TCMonad (Value, Morphism)
evaluate circ e =
  do st <- get
     let gl = globalCxt $ lcontext st
         (r, s) = runState (runExceptT $ eval e)
                  ES{morph = circ, evalEnv = gl, localEvalEnv = Map.empty, gcSize = 10000}
     case r of
       Left e -> throwError $ EvalErr e
       Right r -> return (r, morph s)

-- | Evaluate a parameter term and return a value. 
evaluation :: EExp -> TCMonad Value
evaluation e =
  do st <- get
     let gl = globalCxt $ lcontext st
         (r, _) = runState (runExceptT $ eval e)
                  ES{morph = Morphism VStar [] VStar, evalEnv = gl, localEvalEnv = Map.empty,
                     gcSize = 10000}
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
       evalEnv :: Context,  -- ^ The global evaluation context.
       localEvalEnv :: Map Variable (Value, Integer, Integer, [Variable]),
       gcSize :: Integer
     }

-- | Evaluate an expression to
-- a value in the value domain. The eval function also takes an environment
-- as argument and form a closure when evaluating a lambda abstraction or a lifted term.

eval :: EExp -> Eval Value
-- eval a | trace ("eval:" ++ show (disp a)) False = undefined
eval (EVar x) = do
  v <- lookupLEnv x 
  return v

eval EStar = return VStar
eval EUnit = return VUnit
eval a@(EConst k) =
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

eval (EBase k) = return $ VBase k

eval a@(ELBase k) =
  do st <- get
     let genv = evalEnv st
     case Map.lookup k genv of
       Nothing -> throwError $ UndefinedId k
       Just e ->
         case identification e of
           DataType Simple _ (Just (ELBase id)) -> return (VLBase id)
           DataType (SemiSimple _) _ (Just d) -> eval d
           DataType _ _ Nothing -> return (VBase k)

eval (EForce m) =
  do m' <- eval m
     case m' of
       VLift _ e -> eval e
       w@(VLiftCirc _) -> return w
       v@(VApp VUnBox _) -> return $ VForce v

eval (ETensor e1 e2) =
  do e1' <- eval e1
     e2' <- eval e2
     return $ VTensor e1' e2'

eval a@(ELam ws body) = return (VLam ws body)
     
eval a@(ELift ws body) = return (VLift ws body)
     
eval EUnBox = return VUnBox
eval ERevert = return VRevert
eval a@(EBox) = return VBox
eval a@(EExBox) = return VExBox
eval ERunCirc = return VRunCirc

eval (EApp m n) =
  do v <- eval m
     w <- eval n
     v `seq` w `seq` evalApp v w

eval (EPair m n) = 
  do v <- eval m
     w <- eval n
     v `seq` w `seq` return (VPair v w)

eval (ELet m bd) =
  do m' <- eval m
     open bd $! \ x n ->
       do addDefinition x m'
          m' `seq` eval n


eval (ELetPair m (Abst xs n)) =
  do m' <- eval m
     let r = unVPair (length xs) m'
     case r of
       Just vs -> do
         mapM_ (\ (x, y) -> addDefinition x y)
                        (zip xs vs)
         eval n
       Nothing -> throwError $! TupleMismatch (map fst xs) m'


eval (ELetPat m bd) =
  do m' <- eval m
     case vflatten m' of
       Nothing -> error ("from LetPat" ++ (show $! disp m'))
       Just (Left id, args) ->
         open bd $! \ p m ->
         case p of
           EPApp kid vs
             | kid == id ->
               do let vs' = vs 
                      subs = (zip vs' args)
                  mapM_ (\ (x, v) -> addDefinition x v) subs
                  eval m
           p -> error "pattern mismatch, from eval ELetPat" 
             -- throwError $! PatternMismatch p m'

eval b@(ECase m (EB bd)) =
  do m' <- eval m
     case vflatten m' of
       Nothing -> error ("from eval (Case):") -- ++ (show $! disp b))
       Just (Left id, args) ->
         reduce id args bd
  where reduce id args (bd:bds) =
          open bd $! \ p m ->
          case p of
             EPApp kid vs
               | kid == id -> 
               do st <- get
                  let vs' = vs
                      subs = zip vs' args
                  mapM_ (\ (x, v) -> addDefinition x v) subs
                  eval m
               | otherwise -> reduce id args bds
        reduce id args [] = error "missing branch during eval"
          -- throwError $! MissBranch id b

-- eval a@(Pos _ e) = error "position in eval"
eval a = error $! "from eval: "
         -- ++ (show $! disp a)

-- * Helper functions for eval.

-- | Look up a value from the local environment.

lookupLEnv x =
  do st <- get
     let lenv = localEvalEnv st
         size = gcSize st
     case Map.lookup x lenv of
       Nothing -> error $ "from lookupLEnv:" ++ show x
                  -- ++ (show $ disp lenv)
                  
       Just (v, n, ref, ps) | toInteger (Map.size lenv) <= size ->
         do let lenv' = Map.insert x (v, n-1, ref, ps) lenv
            put st{localEvalEnv = lenv'}
            return v
       Just (v, n, ref, ps) | otherwise ->
         do let lenv' = Map.insert x (v, n-1, ref, ps) lenv
                lenv'' = garbageCollection lenv'
                afterGCSize = toInteger (Map.size lenv'')
                size' = if afterGCSize >= size then afterGCSize+10000
                        else if size - afterGCSize < 1000 then size+10000 else size
            put st{localEvalEnv = lenv'', gcSize = size'}
            return v    

addDefinition (x, n) m =
  do st <- get
     let vs = vars m
         lenv = localEvalEnv st
         lenv' = if n == 0 then lenv
                 else Map.insert x (m, n, 0, vs) (addRef vs lenv) 
     put st{localEvalEnv = lenv'}


addRef [] lenv = lenv
addRef (v:vs) lenv =
  case Map.lookup v lenv of
    Nothing -> error "from addRef"
    Just (val, n, ref, ps) ->
      let lenv' = Map.insert v (val, n , ref+1, ps) lenv
      in addRef vs lenv'
  
-- | A helper function for evaluating various of applications.
evalApp :: Value -> Value -> Eval Value

evalApp VUnBox v | Wired _ <- v = return $! VApp VUnBox v
evalApp VUnBox v | otherwise = return VUnBox
evalApp (VForce (VApp VUnBox v)) w =
  case v of
    Wired bd ->
      open bd $! \ wires m ->
      case m of
        f@(VCircuit (Morphism ins gs outs)) ->
          let binding = makeBinding ins w 
          in appendMorph binding (Morphism ins gs outs)
    a -> error $! "evalApp(Unbox ..) " ++ (show $! disp a)

evalApp (VApp (VApp (VApp VBox q) _) _) v =
  case v of
    VLift _ m -> evalBox m q
    VApp VUnBox w -> return w

evalApp (VApp (VApp (VApp (VApp VExBox q) _) _) _) v =  
  case v of
    VLift _ body ->
      evalExbox body q

evalApp (VApp (VApp (VApp VRunCirc  _) _) (Wired (Abst _ (VCircuit m)))) input =
  case runCircuit m input of
    Left e -> throwError $! SimulationErr e
    Right r -> return r


evalApp (VApp (VApp VRevert _) _) m' =
  case m' of
    Wired bd ->
      open bd $! \ ws (VCircuit (Morphism ins gs outs)) ->
      let gs' = revGates gs in
        return $! Wired (abst ws (VCircuit $! Morphism outs gs' ins))

evalApp a@(Wired _) w = return a

evalApp v w = 
  let (h, res) = unwindVal v
  in case h of
    VLam _ bd -> handleBody (res ++ [w]) bd
    VLiftCirc (Abst vs (Abst lenv e)) -> 
        do let args = res ++ [w]
               lvs = length vs
           if lvs > (length args) then
             return $! VApp v w
             else do let ns = countVar vs e
                         sub = filter (\ (_ , (v, n)) -> n /= 0) $ zip vs (zip args ns)
                         sub' = zip vs args
                         ws = drop lvs args
                         lenv' = updateCirc sub' lenv
                     mapM_ (\(x, (v, n)) -> addDefinition (x, n) v) (lenv' ++ sub)
                     e' <- eval e
                     case e' of
                       VLam _ bd -> handleBody ws bd
                       _ -> return $! foldl VApp e' ws
        
    _ -> return $! VApp v w
          
  where unwindVal (VApp t1 t2) =
          let (h, args) = unwindVal t1
          in (h, args++[t2])
        unwindVal a = (a, [])
        -- Handle beta reduction
        handleBody args bd = open bd $! \ vs m ->
             let --- args = res ++ [w]
                 lvs = length vs
             in
              if lvs > length args
              then return $! VApp v w
              else do let sub = zip vs args
                          ws = drop lvs args
                      mapM_ (\ (x,v) -> addDefinition x v) sub
                      if null ws then eval m
                        else 
                        do m' <- eval m
                           m' `seq` ws `seq` return $! foldl' VApp m' ws
        -- Perform substitution on the variables in a circuit.
        updateCirc :: [(Variable, Value)] -> LEnv -> [(Variable, (Value, Integer))]
        updateCirc sub lenv =
             let (x, (circ, n)):[] = Map.toList lenv
                 Wired (Abst wires (VCircuit (Morphism ins
                                               [Gate id params gin gout ctrls] outs)))
                   = circ
                 params' = helper params sub
                 ctrls':[] = helper [ctrls] sub
                 circ' = Wired (abst wires
                                 (VCircuit (Morphism ins
                                             [Gate id params' gin gout ctrls'] outs)))
             in [(x, (circ', n))]
        -- Perfrom substitution.             
        helper :: [Value] -> [(Variable, Value)] -> [Value]
        helper [] lc = []
        helper (VStar:xs) lc = VStar:helper xs lc
        helper ((VVar x):xs) lc =
             let res = helper xs lc in
             case lookup x lc of
               Just v -> v:res
               Nothing -> error $! "can't find variable " ++ (show $! disp x)

-- | Evaluate a box term.
evalBox :: EExp -> Value -> Eval Value               
evalBox body uv =
  freshLabels (genNames uv) $! \ vs ->
   do st <- get
      b <- eval body
      let uv' = toVal uv vs
          d = Morphism uv' [] uv'
          (res, st') = runState (runExceptT $! evalApp b uv') st{morph = d}
      case res of
        Left e -> throwError e
        Right res' -> 
          let Morphism ins gs _ = morph st'
              newMorph = Morphism ins (reverse gs) res'
              wires = getAllWires newMorph
              morph' = Wired $! abst wires (VCircuit newMorph)
          in return morph'

-- | Evaluate an existsBox term. Note that
-- it is tempting to combine 'evalExbox' and 'evalBox' into one function,
-- but this will introduce bug, because we do not distinguish existential
-- pair and the usual tensor pair at runtime, the evaluator may confuse
-- the tensor pair with existential pair, thus making the wrong decision.
-- So we define 'evalExbox' and 'evalBox' separately to enforce the assumptions.
evalExbox :: EExp -> Value -> Eval Value        
evalExbox body uv =
  freshLabels (genNames uv) $! \ vs ->
   do st <- get
      b <- eval body
      let uv' = toVal uv vs
          d = Morphism uv' [] uv'
          (res, st') = runState (runExceptT $! evalApp b uv') st{morph = d}
      case res of
        Left e -> throwError e
        Right (VPair n res') -> 
          let Morphism ins gs _ = morph st'
              newMorph = Morphism ins (reverse gs) res'
              wires = getAllWires newMorph
              morph' = Wired $! abst wires (VCircuit newMorph)
          in return (VPair n morph')        
        Right a -> error $! "from eval_exBox\n" ++ (show $! disp a)



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
       error ("binding mismatch!\n" ++ (show $! disp w) ++
               "\n" ++ (show $! disp v))
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
invertName id =  Id $! getName id ++ "*"


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
     return $! VApp e1' e2'

templateToVal (VTensor e1 e2) =
  do e1' <- templateToVal e1
     e2' <- templateToVal e2
     return $! VPair e1' e2'

templateToVal a = error "applying templateToVal function to an ill-formed template"

-- | Get the size of a simple data type.
size :: Num a => Value -> a
size (VLBase x) = 1
size (VConst _) = 0
size VUnit = 0
size (VApp e1 e2) = size e1 + size e2
size (VTensor e1 e2) = size e1 + size e2
size a = error $! "applying size function to an ill-formed template:" ++ (show $! disp a)     

-- | Obtain all the labels from the circuit.
getAllWires :: Morphism -> [Label]
getAllWires (Morphism ins gs outs) =
  let inWires = S.fromList $! getWires ins
      outWires = S.fromList $! getWires outs
      gsWires = S.unions $! map getGateWires gs
  in S.toList (inWires `S.union` outWires `S.union` gsWires)
  where getGateWires (Gate _ _ ins outs ctrls) =
          S.fromList (getWires ins) `S.union`
          S.fromList (getWires outs) `S.union`
          S.fromList (getWires ctrls)

-- | Obtain a submap from a map /m/ with domain /vs/.
subMap !m !vs =
  let ns = Map.keys m \\ vs
  in ns `seq` foldl' (\ m n -> Map.delete n m) m ns

  -- let m' = map (\ k -> case Map.lookup k m of
  --                        Just v -> (k, v)
  --                        Nothing -> error $! "from subMap, can't find:" ++ show k
  --              ) vs
  --     m'' = Map.fromList m'
  -- in m''

-- deleteMap !m =
--   let ns = Map.keys m
--   in ns `seq` foldl' (\ m n -> Map.delete n m) m ns

garbageCollection lenv =
  let lenv' = Map.foldlWithKey' (\ m k (_, n, ref, ps) -> tryDelete k n ref ps m) lenv lenv
  in lenv'
  where
        tryDelete k n ref ps m | n <= 0 && ref <= 0 =
          let m' = Map.delete k m
              m'' = decrRef ps m'
          in m''
        tryDelete k n ref ps m | otherwise = m
        decrRef [] m = m
        decrRef (v:vs) m =
          case Map.lookup v m of
            Nothing -> error "from decrRef"
            Just (val, n, ref, ps) ->
              let m' = Map.insert v (val, n, ref-1, ps) m
              in decrRef vs m'
        
                             
          
