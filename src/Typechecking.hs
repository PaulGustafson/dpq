module Typechecking where

import Syntax
import SyntacticOperations
import TCMonad
import TypeError
import Utils
import Normalize
import Substitution


import Nominal
import qualified Data.Set as S

import Control.Monad.Except
import Control.Monad.State

-- | The flag indicate if whether it is during kinding or not.
typeCheck :: Bool -> Exp -> Exp -> TCMonad (Exp, Exp)
typeInfer :: Bool -> Exp -> TCMonad (Exp, Exp)

typeInfer flag (Pos p e) =
  do (ty, ann) <- typeInfer flag e `catchError` \ e -> throwError $ addErrPos p e
     return (ty, (Pos p ann))

typeInfer flag Set = return (Sort, Set)

typeInfer flag a@(Base kid) =
  lookupId kid >>= \ x -> return (classifier x, a)

typeInfer flag a@(LBase kid) =
  lookupId kid >>= \ x -> return (classifier x, a)

typeInfer flag a@(Var x) =
  do (t, _) <- lookupVar x
     if flag then
       do t' <- shape t 
          return (t', a)
       else
       do updateCount x
          return (t, a)

typeInfer flag a@(EigenVar x) =
  do (t, _) <- lookupVar x
     if flag then
       do t' <- shape t 
          return (t', a)
       else
       do updateCount x
          return (t, a)
     
typeInfer flag a@(Const kid) =
  do funPac <- lookupId kid
     let cl = classifier funPac
     return (cl, a)

typeInfer flag a@(App t1 t2) =
  do (t', ann) <- typeInfer flag t1
     if isKind t'
       then handleTypeApp ann t' t1 t2 
       else handleTermApp flag ann t1 t' t1 t2

typeInfer False a@(UnBox) =
  freshNames ["a", "b"] $ \ [a, b] ->
  let va = Var a
      vb = Var b
      t1 = Arrow (Circ va vb) (Bang (Arrow va vb))
      ty = Forall (abst [a, b] t1) Set
  in return (ty, UnBox)

typeInfer False a@(Revert) =
  freshNames ["a", "b"] $ \ [a, b] ->
  let va = Var a
      vb = Var b
      t1 = Arrow (Circ va vb) (Circ vb va)
      ty = Forall (abst [a, b] t1) Set
  in return (ty, Revert)

typeInfer False t@(Box) = freshNames ["a", "b"] $ \ [a, b] ->
  do let va = Var a
         vb = Var b
         simpClass = Id "Simple"
         t1 = Arrow (Bang (Arrow va vb)) (Circ va vb)
         t1' = Imply [App' (Base simpClass) va , App' (Base simpClass) vb] t1
         boxType = Pi (abst [a] (Forall (abst [b] t1') Set)) Set
     return (boxType, t)

typeInfer False t@(RunCirc) = freshNames ["a", "b", "c", "d"] $ \ [a, b, c, d] ->
  do let va = Var a
         vb = Var b
         vc = Var c
         vd = Var d
         simpParam = Id "SimpParam"
         t1 = Arrow (Circ va vb) (Arrow vc vd)
         t1' = Imply [App' (App' (Base simpParam) va) vc , App' (App' (Base simpParam) vb) vd] t1
         res = Forall (abst [a, b, c, d] t1') Set
     return (res, t)

typeInfer flag t@(ExBox) =
  freshNames ["a", "b", "p", "n"] $ \ [a, b, p, n] ->
  do let va = Var a
         vb = Var b
         vp = Var p
         vn = Var n
         simpClass = Id "Simple"
         paramClass = Id "Parameter"
         kp = Arrow (vb) Set
         simpA = App' (Base simpClass) va
         paramB = App' (Base paramClass) vb
         simpP = App' (Base simpClass) (App' vp vn)
         t1Output = Exists (abst n (App' vp vn)) (vb)
         t1 = Bang (Arrow va t1Output)
         output = Exists (abst n $ Imply [simpP] (Circ va (App' vp vn))) (vb)
         beforePi = Arrow t1 output
         r = Pi (abst [a] $
                 Forall (abst [b] (Imply [paramB] $ Pi (abst [p] $ Imply [simpA] beforePi) kp)) Set) Set
     return (r, t)

typeInfer flag Star = return (Unit, Star)
typeInfer flag Unit = return (Set, Unit)

typeInfer flag a@(Pair t1 t2) =
  do (ty1, ann1) <- typeInfer flag t1 
     (ty2, ann2) <- typeInfer flag t2
     return (Tensor ty1 ty2, Pair ann1 ann2)




typeCheck flag (Pos p e) ty =
  do (ty', ann) <- typeCheck flag e ty `catchError` \ e -> throwError $ addErrPos p e
     return (ty', Pos p ann)







handleTypeApp ann t' t1 t2 =
  case erasePos t' of
    Arrow k1 k2 ->
        do (_, ann2) <- typeCheck True t2 k1
           return (k2, App' ann ann2)
    Pi b ty ->
      open b $ \ vs b' ->
        do (_, ann2) <- typeCheck True t2 ty
           let fvs = S.toList $ getVars NoEigen ann2
               su = zip fvs (map EigenVar fvs)
               t2' = erasePos $ apply su ann2
           b'' <- betaNormalize (apply [(head vs, t2')]  b')
           let k2 = if null (tail vs) then b''
                      else Pi (abst (tail vs) b'') ty
           return (k2, App' ann ann2)
    a -> throwError $ KAppErr t1 (App t1 t2) a  

-- | The handleTermApp function produces
-- annotation for an application term expression.
handleTermApp flag ann pos t' t1 t2 = 
  do (a1', rt, anEnv) <- addAnn flag pos ann t' []
     mapM (\ (x, t) -> addVar x t) anEnv
     case rt of
       Arrow ty1 ty2 ->
         do (_, ann2) <- typeCheck flag t2 ty1
            let res = if flag then App' a1' ann2 else App a1' ann2
            return (ty2, res)
       b@(Pi bind ty) ->
         -- Note that here updateWithSubst is necessary
         -- as we do not want variables in bind to escape
         -- the current scope.
         open bind $
         \ xs m -> 
                -- typecheck or kind check t2
                -- since t2 may travels to m, we
                -- normalize [[t2]/x]m
             do let flag' = isKind ty
                (_, kann) <- typeCheck flag' t2 ty
                let vs = S.toList $ getVars NoEigen kann
                    su = zip vs (map EigenVar vs)
                    t2' = erasePos $ apply su kann
                m' <- betaNormalize (apply [(head xs, t2')] m)
                m'' <- if flag then shape m' else return m'
                let res = if flag then AppDep' a1' kann
                          else AppDep a1' kann
                if null (tail xs)
                  then
                  do m''' <- updateWithSubst m''
                     res' <- updateWithSubst res
                     return (m''', res')
                  else
                  do m''' <- updateWithSubst m''
                     ty' <- updateWithSubst ty
                     res' <- updateWithSubst res
                     return (Pi (abst (tail xs) m''') ty', res')
       b -> throwError $ ArrowErr t1 b



addAnn flag e a (Pos _ t) env = addAnn flag e a t env

addAnn flag e a (Bang t) env =
  let force = if flag then Force' else Force
  in addAnn flag e (force a) t env

addAnn flag e a (Forall bd ty) env | isKind ty = open bd $ \ xs t ->
       let a' = foldl AppType a (map Var xs)
           new = map (\ x -> (x, ty)) xs
       in addAnn flag e a' t (new ++ env)

addAnn flag e a (Forall bd ty) env | otherwise = open bd $ \ xs t ->
       let a' = foldl AppTm a (map Var xs)
           new = map (\ x -> (x, ty)) xs
       in addAnn flag e a' t (new ++ env)

addAnn flag e a (Imply bds ty) env =
  do ts <- get
     let i = clock ts
         ns = zipWith (\ i b -> "#goalinst"++(show i)) [i .. ] bds
     freshNames ns $ \ ns ->
       do let instEnv = map (\ x -> (x, e)) (zip ns bds) 
              i' = i + length bds
          put ts{clock = i'}
          mapM_ (\ ((x, t), e) -> addGoalInst x t e) instEnv
          let a' = foldl AppDict a (map GoalVar ns)
          addAnn flag e a' ty env
    
addAnn flag e a t env = return (a, t, env)  
