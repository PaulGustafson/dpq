module Unification where

import Syntax
import Substitution
import Utils
import SyntacticOperations


import qualified Data.Set as S
import qualified Data.Map as Map
import Control.Monad.State
import Debug.Trace

  
runUnify :: Exp -> Exp -> Maybe Subst
-- runUnify t1 t2 | trace ((show $ disp t1) ++ ":" ++ (show $ disp t2)) $ False = undefined
runUnify t1 t2 =
  let t1' = erasePos t1
      t2' = erasePos t2
      (r, s) = runState (unify t1' t2') Map.empty
  in if r then Just s else Nothing

-- | Implement the usual syntactic unification
unify :: Exp -> Exp -> State Subst Bool
unify Unit Unit = return True
unify Set Set = return True
unify (Base x) (Base y) | x == y = return True
                        | otherwise = return False
unify (LBase x) (LBase y) | x == y = return True
                          | otherwise = return False
unify (Const x) (Const y) | x == y = return True
                          | otherwise = return False


unify (EigenVar x) (EigenVar y) | x == y = return True
                                | otherwise = return False


unify (Var x) t
  | Var x == t = return True
  | (EigenVar y) <- t, x == y = return True
  | x `S.member` getVars AllowEigen t = return False
  | otherwise = 
    do sub <- get
       let subst' = mergeSub (Map.fromList [(x, t)]) sub
       put subst'
       return True

unify t (Var x)
  | Var x == t = return True
  | (EigenVar y) <- t, x == y = return True  
  | x `S.member` getVars AllowEigen t = return False
  | otherwise =
    do sub <- get
       let subst' = mergeSub (Map.fromList [(x, t)]) sub
       put subst'
       return True


unify (GoalVar x) t
  | GoalVar x == t = return True
  | x `S.member` getVars GetGoal t = return False
  | otherwise = 
    do sub <- get
       let subst' = mergeSub (Map.fromList [(x, t)]) sub
       put subst'
       return True

unify t (GoalVar x) 
  | GoalVar x == t = return True
  | x `S.member` getVars GetGoal t = return False
  | otherwise = 
    do sub <- get
       let subst' = mergeSub (Map.fromList [(x, t)]) sub
       put subst'
       return True


-- We allow unifying two first-order existential types.  
unify (Exists (Abst x m) ty1) (Exists (Abst y n) ty2) =
  do r <- unify ty1 ty2
     if r then freshNames ["#existUnif"] $ \ (e:[]) ->
       do let m' = apply [(x, EigenVar e)] m
              n' = apply [(x, EigenVar e)] n
          sub <- get
          unify (substitute sub m') (substitute sub n')
       else return False

-- We also allow unifying two case expression,
-- but only a very simple kind of unification
unify (Case e1 (B br1)) (Case e2 (B br2)) | br1 == br2 =
  unify e1 e2

     
unify (Arrow t1 t2) (Arrow t3 t4) =
  do a <- unify t1 t3
     if a
       then do sub <- get
               unify (substitute sub t2) (substitute sub t4)
       else return False

unify (Arrow' t1 t2) (Arrow' t3 t4) =
  do a <- unify t1 t3
     if a
       then do sub <- get
               unify (substitute sub t2) (substitute sub t4)
       else return False

unify (Tensor t1 t2) (Tensor t3 t4) =
  do a <- unify t1 t3
     if a
       then do sub <- get
               unify (substitute sub t2) (substitute sub t4)
       else return False

unify (Circ t1 t2) (Circ t3 t4) =
  do a <- unify t1 t3
     if a
       then do sub <- get
               unify (substitute sub t2) (substitute sub t4)
       else return False

unify (Bang t) (Bang t') = unify t t'
unify (Force t) (Force t') = unify t t'
unify (Force' t) (Force' t') = unify t t'
unify (Lift t) (Lift t') = unify t t'

unify (App t1 t2) (App t3 t4) =
  do a <- unify t1 t3
     if a
       then
       do sub <- get
          unify (substitute sub t2) (substitute sub t4)
       else return False

unify (App' t1 t2) (App' t3 t4) =
  do a <- unify t1 t3
     if a
       then
       do sub <- get
          unify (substitute sub t2) (substitute sub t4)
       else return False

unify (AppDict t1 t2) (AppDict t3 t4) =
  do a <- unify t1 t3
     if a
       then
       do sub <- get
          unify (substitute sub t2) (substitute sub t4)
       else return False

unify (AppDep t1 t2) (AppDep t3 t4) =
  do a <- unify t1 t3
     if a
       then
       do sub <- get
          unify (substitute sub t2) (substitute sub t4)
       else return False


unify (AppType t1 t2) (AppType t3 t4) =
  do a <- unify t1 t3
     if a
       then do sub <- get
               unify (substitute sub t2) (substitute sub t4)
       else return False

unify (AppTm t1 t2) (AppTm t3 t4) =
  do a <- unify t1 t3
     if a
       then do sub <- get
               unify (substitute sub t2) (substitute sub t4)
       else return False


unify t t' = return False



