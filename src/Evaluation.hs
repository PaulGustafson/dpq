module Evaluation where

import Syntax
import Utils
import Nominal


import qualified Data.Map as Map
import Data.Map (Map)


data EvalState =
  ES { morph :: Morphism, -- ^ underlying incomplete circuit.
       evalEnv :: Context  -- ^ global evaluation context.
     }

data EvalError = MissBranch Id Exp
               | UndefinedId Id 
               | PatternMismatch Pattern Exp
               | TupleMismatch [Variable] Exp

type Eval a = ExceptT EvalError (State EvalState) a

evaluation :: EvalState -> Eval a -> TCMonad a
evaluation d body =
  runState (runExceptT body) d

eval :: Map Variable Exp -> Exp -> Eval Exp
eval = undefined



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

