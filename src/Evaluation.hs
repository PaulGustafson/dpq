module Evaluation where

import Syntax
import Utils
import Nominal
import TCMonad
import TypeError


import Control.Monad.State
import Control.Monad.Identity
import Control.Monad.Except

import qualified Data.Map as Map
import Data.Map (Map)


data EvalState =
  ES { morph :: Morphism, -- ^ underlying incomplete circuit.
       evalEnv :: Context  -- ^ global evaluation context.
     }


type Eval a = ExceptT EvalError (State EvalState) a

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
           DefinedFunction Nothing -> throwError $ UndefinedId k
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
     eval_app lenv v w

eval lenv a = error $ "from eval: " ++ (show $ disp a)


eval_app lenv UnBox v = return $ App UnBox v
eval_app lenv (App UnBox v) w =
  case v of
    Wired bd ->
      open bd $ \ wires m ->
      case m of
        f@(Morphism ins gs outs) ->
          let binding = makeBinding ins w 
          in appendMorph binding f
    a -> error $ "eval_app(Unbox ..) " ++ (show $ disp a)

eval_app lenv (AppDict (AppDict (AppDep Box q) _) _) v =
  do st <- get
     let genv = evalEnv st
     uv <- eval lenv q
     eval_box lenv v uv


eval_app lenv (AppDict (AppDep (AppDict (AppDep ExBox q) _) _) _) v =  
  do st <- get
     let genv = evalEnv st
     uv <- eval lenv q
     eval_exbox lenv v uv

eval_app lenv Revert m' =
  case m' of
    Wired bd ->
      open bd $ \ ws (Morphism ins gs outs) ->
      let gs' = revGates gs in
        return $ Wired (abst ws (Morphism outs gs' ins))

eval_app lenv a@(Wired _) (Const id) | getIdName id == "SimpleDict" =
  return a

eval_app lenv v w =
  let (h, res) = unwind v
  in case h of
      Lam bd -> handleBody res bd
      LamV bd -> handleBody res bd
      a -> return $ App v w
     where handleBody res bd = open bd $ \ vs m ->
             let args = res ++ [w]
                 lvs = length vs
             in
              if lvs > length args
              then return $ App v w
              else do let sub = zip vs args
                          ws = drop lvs args
                          lenv' = foldr (\ (x,v) y -> Map.insert x v y) lenv sub
                      eval lenv' (foldl App m ws)






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

