{-# LANGUAGE FlexibleInstances, FlexibleContexts#-}
module Evaluation where

import Syntax
import SyntacticOperations
import Utils
import Nominal
import TCMonad
import TypeError


import Control.Monad.State
import Control.Monad.Identity
import Control.Monad.Except

import qualified Data.Map as Map
import Data.Map (Map)
import Data.Set (Set)
import qualified Data.Set as Set

data EvalState =
  ES { morph :: Morphism, -- ^ underlying incomplete circuit.
       evalEnv :: Context  -- ^ global evaluation context.
     }


type Eval a = ExceptT EvalError (State EvalState) a

-- | A cheap way to embed TCMonad into Eval. 
tcToEval :: TCMonad a -> Eval a
tcToEval m =
  do st <- get
     let cxt = evalEnv st
         (res, tySt) = runIdentity $ runTCMonadT cxt [] m
     case res of
       Left e -> throwError $ ErrWrapper e
       Right a -> return a

    
evaluation :: Exp -> TCMonad Exp
evaluation e =
  do st <- get
     let gl = globalCxt $ lcontext st
         (r, _) = runState (runExceptT $ eval Map.empty e)
                  ES{morph = Morphism Star [] Star, evalEnv = gl}
     case r of
       Left e -> throwError $ EvalErr e
       Right r -> return r

lookupLEnv = undefined

eval :: Map Variable Exp -> Exp -> Eval Exp
eval lenv (Var x) =
  return $ lookupLEnv x lenv 
eval lenv (EigenVar x) =
  return $ lookupLEnv x lenv 
eval lenv Star = return Star
eval lenv (Base k) = return (Base k)

eval lenv a@(Const k) =
  do st <- get
     let genv = evalEnv st
     case Map.lookup k genv of
       Nothing -> throwError $ UndefinedId k
       Just e ->
         case identification e of
           DataConstr _ -> return a
           DefinedGate e -> return e
           -- DefinedFunction Nothing -> throwError $ UndefinedId k
           DefinedFunction (Just (_, v, _)) -> return v
           DefinedMethod _ e -> return e
           DefinedInstFunction _ e -> return e

eval lenv a@(LBase k) =
  do st <- get
     let genv = evalEnv st
     case Map.lookup k genv of
       Nothing -> throwError $ UndefinedId k
       Just e ->
         case identification e of
           DataType Simple _ (Just e) -> return e
           DataType _ _ Nothing -> return a
           DictionaryType _ _ -> return a

eval lenv (Force m) =
  do m' <- eval lenv m
     case m' of
       Lift n -> eval lenv n
       v@(App UnBox _) -> return $ Force v
       _ -> error "from force"

eval lenv (Force' m) =
  do m' <- eval lenv m
     case m' of
       Lift n -> tcToEval (shape n) >>= eval lenv 
       _ -> error "from force'"

eval lenv a@(Lam body) = 
  if Map.null lenv then return a else return $ instantiate lenv a

eval lenv a@(Lam' body) = 
  if Map.null lenv then return a else return $ instantiate lenv a

eval lenv a@(LamDep body) = 
  if Map.null lenv then return a else return $ instantiate lenv a

eval lenv a@(LamDep' body) = 
  if Map.null lenv then return a else return $ instantiate lenv a

eval lenv a@(LamDict body) = 
  if Map.null lenv then return a else return $ instantiate lenv a

eval lenv UnBox = return UnBox
eval lenv Revert = return Revert
eval lenv a@(Box) = return a
eval lenv a@(ExBox) = return a
eval lenv a@(Wired _) = return a
eval lenv a@(Pos _ e) = eval lenv e

eval lenv (App m n) =
  do v <- eval lenv m
     w <- eval lenv n
     evalApp lenv v w

eval lenv (AppDep m n) =
  do v <- eval lenv m
     w <- eval lenv n
     evalAppDep lenv v w

eval lenv (App' m n) =
  do v <- eval lenv m
     w <- eval lenv n
     evalApp' lenv v w

eval lenv (AppDep' m n) =
  do v <- eval lenv m
     w <- eval lenv n
     evalAppDep' lenv v w

eval lenv (AppDict m n) =
  do v <- eval lenv m
     w <- eval lenv n
     evalAppDict lenv v w

eval lenv (Let m bd) =
  do m' <- eval lenv m
     open bd $ \ x n ->
        let lenv' = Map.insert x m' lenv
        in eval lenv' n


eval lenv (LetPair m (Abst xs n)) =
  do m' <- eval lenv m
     let r = unPair (length xs) m'
     case r of
       Just vs -> do
         let lenv' = foldl (\ a (x, y) -> Map.insert x y a)
                       lenv (zip xs vs)
         eval lenv' n
       Nothing -> throwError $ TupleMismatch xs m'


eval lenv (LetPat m bd) =
  do m' <- eval lenv m
     case flatten m' of
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
     case flatten m' of
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


eval lenv a = error $ "from eval: " ++ (show $ disp a)


evalApp lenv UnBox v = return $ App UnBox v
evalApp lenv (App UnBox v) w =
  case v of
    Wired bd ->
      open bd $ \ wires m ->
      case m of
        f@(Morphism ins gs outs) ->
          let binding = makeBinding ins w 
          in appendMorph binding f
    a -> error $ "evalApp(Unbox ..) " ++ (show $ disp a)

evalApp lenv (AppDict (AppDict (AppDep Box q) _) _) v =
  do st <- get
     let genv = evalEnv st
     uv <- eval lenv q
     evalBox lenv v uv


evalApp lenv (AppDict (AppDep (AppDict (AppDep ExBox q) _) _) _) v =  
  do st <- get
     let genv = evalEnv st
     uv <- eval lenv q
     evalExbox lenv v uv

evalApp lenv Revert m' =
  case m' of
    Wired bd ->
      open bd $ \ ws (Morphism ins gs outs) ->
      let gs' = revGates gs in
        return $ Wired (abst ws (Morphism outs gs' ins))

evalApp lenv a@(Wired _) (Const id) | getName id == "SimpleDict" =
  return a

evalApp lenv v w = handleApplication AppFlag lenv v w

evalApp' lenv v w = handleApplication App'Flag lenv v w


evalAppDep lenv v w = handleApplication AppDepFlag lenv v w
evalAppDep' lenv v w = handleApplication AppDep'Flag lenv v w
evalAppDict lenv v w = handleApplication AppDictFlag lenv v w

handleApplication appflag lenv v w = 
  let (h, res) = unwind appflag v
  in case h of
      Lam bd -> handleBody App res bd
      Lam' bd -> handleBody App' res bd
      LamDep' bd -> handleBody AppDep' res bd
      LamDep bd -> handleBody AppDep res bd
      LamDict bd -> handleBody AppDict res bd
      _ ->
        case appflag of
          AppFlag -> return $ App v w
          App'Flag -> return $ App' v w
          AppDep'Flag -> return $ AppDep' v w
          AppDepFlag -> return $ AppDep v w
          AppDictFlag -> return $ AppDict v w
          
     where handleBody app res bd = open bd $ \ vs m ->
             let args = res ++ [w]
                 lvs = length vs
             in
              if lvs > length args
              then return $ app v w
              else do let sub = zip vs args
                          ws = drop lvs args
                          lenv' = foldr (\ (x,v) y -> Map.insert x v y) lenv sub
                      eval lenv' (foldl app m ws)


evalBox lenv body uv =
  freshNames (genNames uv) $ \ vs ->
   do st <- get
      let uv' = toVal uv vs
          d = Morphism uv' [] uv'
          (res, st') = runState (runExceptT $ eval lenv (App body uv')) st{morph = d}
      case res of
        Left e -> throwError e
        Right res' -> 
          let Morphism ins gs _ = morph st'
              newMorph = Morphism ins (reverse gs) res'
              wires = getAllWires newMorph
              morph' = Wired $ abst wires newMorph
          in return morph'


evalExbox lenv body uv =
  freshNames (genNames uv) $ \ vs ->
   do st <- get
      let uv' = toVal uv vs
          d = Morphism uv' [] uv'
          (res, st') = runState (runExceptT $ eval lenv (App body uv')) st{morph = d}
      case res of
        Left e -> throwError e
        Right (Pair n res') -> 
          let Morphism ins gs _ = morph st'
              newMorph = Morphism ins (reverse gs) res'
              wires = getAllWires newMorph
              morph' = Wired $ abst wires newMorph
          in return (Pair n morph')
        Right a -> error $ "from eval_exBox\n" ++ (show $ disp a)



instantiate :: Map Variable Exp -> Exp -> Exp
instantiate lenv (Unit) = Unit
instantiate lenv (Set) = Set
instantiate lenv Star = Star
instantiate lenv a@(Var x) =
  case Map.lookup x lenv of
       Nothing -> a
       Just v -> v
instantiate lenv a@(Base x) = a
instantiate lenv a@(LBase x) = a
instantiate lenv a@(Const x) = a
instantiate lenv (App e1 e2) = App (instantiate lenv e1) (instantiate lenv e2)
instantiate lenv (AppDep e1 e2) = AppDep (instantiate lenv e1) (instantiate lenv e2)
instantiate lenv (AppDict e1 e2) = AppDict (instantiate lenv e1) (instantiate lenv e2)
instantiate lenv (App' e1 e2) = App' (instantiate lenv e1) (instantiate lenv e2)
instantiate lenv (AppDep' e1 e2) = AppDep' (instantiate lenv e1) (instantiate lenv e2)

instantiate lenv (Tensor e1 e2) = Tensor (instantiate lenv e1) (instantiate lenv e2)
instantiate lenv (Pair e1 e2) = Pair (instantiate lenv e1) (instantiate lenv e2)
instantiate lenv (Arrow e1 e2) = Arrow (instantiate lenv e1) (instantiate lenv e2)
instantiate lenv (Bang e) = Bang $ instantiate lenv e
instantiate lenv (UnBox) = UnBox
instantiate lenv (Revert) = Revert
instantiate lenv a@(Box) = a
instantiate lenv a@(ExBox) = a
instantiate lenv (Lift e) = Lift $ instantiate lenv e
instantiate lenv (Force e) = Force $ instantiate lenv e
instantiate lenv (Force' e) = Force' $ instantiate lenv e
instantiate lenv a@(Wired _) = a 
instantiate lenv (Circ e1 e2) = Circ (instantiate lenv e1) (instantiate lenv e2)
instantiate lenv a@(Pi bd e) = a
instantiate lenv (Lam bd) = Lam (open bd $ \ vs b -> abst vs (instantiate lenv b))
instantiate lenv (LamDep bd) = LamDep (open bd $ \ vs b -> abst vs (instantiate lenv b))
instantiate lenv (LamDep' bd) = LamDep' (open bd $ \ vs b -> abst vs (instantiate lenv b))
instantiate lenv (LamDict bd) = LamDict (open bd $ \ vs b -> abst vs (instantiate lenv b))
instantiate lenv (Lam' bd) = Lam' (open bd $ \ vs b -> abst vs (instantiate lenv b))
instantiate lenv (Let m bd) = Let (instantiate lenv m) (open bd $ \ vs b -> abst vs (instantiate lenv b))
instantiate lenv (LetPair m bd) = LetPair (instantiate lenv m) (open bd $ \ xs b -> abst xs (instantiate lenv b))
instantiate lenv (LetPat m bd) = LetPat (instantiate lenv m)
                                 (open bd $ \ vs b -> abst vs (instantiate lenv b))
instantiate lenv (Case e (B br)) = Case (instantiate lenv e) (B (map helper br))
  where helper bd = open bd $ \ p m -> abst p (instantiate lenv m)


-- | Append a circuit to the underline circuit state according to a Binding
-- For efficiency reason we try prepend instead of append        
appendMorph :: Binding -> Morphism -> Eval Exp
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

rename (Morphism ins gs outs) m =
  let ins' = renameTemp ins m
      outs' = renameTemp outs m
      gs' = renameGs gs m
  in Morphism ins' gs' outs'


renameTemp (Label x) m =
  case Map.lookup x m of
    Nothing -> (Label x)
    Just y -> Label y
renameTemp a@(Const _) m = a
renameTemp Star m = Star
renameTemp (App e1 e2) m = App (renameTemp e1 m) (renameTemp e2 m)
-- renameTemp (AppDep e1 e2) m = AppDep (renameTemp e1 m) (renameTemp e2 m)
renameTemp (Pair e1 e2) m = Pair (renameTemp e1 m) (renameTemp e2 m)
renameTemp a m = error "applying renameTemp function to an ill-formed template"     

renameGs gs m = map helper gs
  where helper (Gate id params ins outs ctrls) =
          Gate id params (renameTemp ins m) (renameTemp outs m) (renameTemp ctrls m)

type Binding = Map Variable Variable


getWires (Label x) = [x]
getWires (Const _) = []
getWires Star = []
getWires (App e1 e2) = getWires e1 ++ getWires e2
-- getWires (AppDep e1 e2) = getWires e1 ++ getWires e2
getWires (Pair e1 e2) = getWires e1 ++ getWires e2
getWires a = error $ "applying getWires function to an ill-formed template:" ++ (show $ disp a)


makeBinding :: Exp -> Exp -> Binding
makeBinding w v =
  let ws = getWires w
      vs = getWires v
  in if length ws /= length vs
     then 
       error ("binding mismatch!\n" ++ (show $ disp w) ++
               "\n" ++ (show $ disp v))
       else Map.fromList (zip ws vs)

revGates :: [Gate] -> [Gate]
revGates xs = revGatesh xs [] 
  where revGatesh [] gs = gs
        revGatesh ((Gate id params ins outs ctrls):res) gs =
          do id' <- invertName id
             revGatesh res ((Gate id' params outs ins ctrls):gs)

invertName id | getName id == "Init0" = return $ Id "Term0"
invertName id | getName id == "Init1" = return $ Id "Term1"
invertName id | getName id == "Term1" = return $ Id "Init1"
invertName id | getName id == "Term0" = return $ Id "Init0"
invertName id | getName id == "H" = return $ Id "H"
invertName id | getName id == "CNot" = return $ Id "CNot"
invertName id | getName id == "Not_g" = return $ Id "Not_g"
invertName id | getName id == "C_Not" = return $ Id "C_Not"
invertName id | getName id == "QNot" = return $ Id "QNot"
invertName id | getName id == "CNotGate" = return $ Id "CNotGate"
invertName id | getName id == "ToffoliGate_10" = return $ Id "ToffoliGate_10"
invertName id | getName id == "ToffoliGate_01" = return $ Id "ToffoliGate_01"
invertName id | getName id == "ToffoliGate" = return $ Id "ToffoliGate"
invertName id | getName id == "Mea" = error "cannot invert Mea gate"
invertName id | getName id == "Discard" = error "cannot invert Discard gate"
invertName id = return $ Id $ getName id ++ "*"


-- | Generate a list of wirenames from a simple data type.
genNames uv =
  let n = size uv
      ls = "l":ls
      names = take n ls
  in names

toVal uv vs = evalState (templateToVal uv) vs

-- | Obtain a fresh template inhabitant of a simple type, with wirenames
-- draw from the state. 
templateToVal :: Exp -> State [Variable] Exp
templateToVal (LBase _) =
  do x <- get
     let (v:vs) = x
     put vs
     return (Label v)
templateToVal a@(Const _) = return a
templateToVal a@(Unit) = return Star
templateToVal (App e1 e2) =
  do e1' <- templateToVal e1
     e2' <- templateToVal e2
     return $ App e1' e2'

templateToVal (Tensor e1 e2) =
  do e1' <- templateToVal e1
     e2' <- templateToVal e2
     return $ Pair e1' e2'

templateToVal a = error "applying templateToVal function to an ill-formed template"

-- | Size of a simple data type.
size (LBase x) = 1
size (Const _) = 0
size Unit = 0
size (App e1 e2) = size e1 + size e2
-- size (AppDep e1 e2) = size e1
size (Tensor e1 e2) = size e1 + size e2
size a = error $ "applying size function to an ill-formed template:" ++ (show $ disp a)     

-- | Obtain all the wire names from the circuit.
getAllWires (Morphism ins gs outs) =
  let inWires = Set.fromList $ getWires ins
      outWires = Set.fromList $ getWires outs
      gsWires = Set.unions $ map getGateWires gs
  in Set.toList (inWires `Set.union` outWires `Set.union` gsWires)
  where getGateWires (Gate _ _ ins outs ctrls) =
          Set.fromList (getWires ins) `Set.union`
          Set.fromList (getWires outs) `Set.union`
          Set.fromList (getWires ctrls)

