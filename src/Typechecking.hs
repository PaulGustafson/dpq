{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
-- | This module implements a bi-directional algorithm for elaborating
-- a surface level language into the core language. The elaborated programs
-- will be checked by the "Proofchecking" module. The elaboration aims for soundness, i.e.,
-- if the elaboration is successful, then it will past the proof-checker. Otherwise it
-- would indicate there is a bug in the elaboration. 


module Typechecking where

import Syntax
import SyntacticOperations
import TCMonad
import TypeError
import Utils
import Normalize
import Substitution
import TypeClass
import Unification

import Nominal
import qualified Data.Set as S
import qualified Data.Map as Map
import Data.Map (Map)
import Debug.Trace
import Control.Monad.Except
import Control.Monad.State

-- | Check an expression against a type. The flag = True indicates
--  it is kinding or sorting, flag = False indicates type checking.
-- For simplicity, we do not allow direct mentioning
-- of lambda, box, unbox, revert, runCirc, existsBox in types (these will give rise to
-- type errors saying no typing rule for inference). 

typeCheck :: Bool -> Exp -> Exp -> TCMonad (Exp, Exp)

-- | Infer a type for a term. 
typeInfer :: Bool -> Exp -> TCMonad (Exp, Exp)

typeInfer flag (Pos p e) =
  do (ty, ann) <- typeInfer flag e `catchError` \ e -> throwError $ addErrPos p e
     return (ty, (Pos p ann))

typeInfer True Set = return (Sort, Set)

typeInfer True a@(Base kid) =
  lookupId kid >>= \ x -> return (classifier x, a)

typeInfer True a@(LBase kid) =
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
      simpClass = Id "Simple"
      t1 = Arrow (Circ va vb) (Bang (Arrow va vb))
      t1' = Imply [App' (Base simpClass) va , App' (Base simpClass) vb] t1
      ty = Forall (abst [a, b] t1') Set
  in return (ty, UnBox)

typeInfer False a@(Revert) =
  freshNames ["a", "b"] $ \ [a, b] ->
  let va = Var a
      vb = Var b
      simpClass = Id "Simple"
      t1 = Arrow (Circ va vb) (Circ vb va)
      t1' = Imply [App' (Base simpClass) va , App' (Base simpClass) vb] t1
      ty = Forall (abst [a, b] t1') Set
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

typeInfer False t@(ExBox) =
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
                 Forall (abst [b] (Imply [simpA, paramB] $ Pi (abst [p] $ beforePi) kp)) Set) Set
     return (r, t)

typeInfer flag Star = return (Unit, Star)
typeInfer flag Unit = return (Set, Unit)

-- Only infering tensor product for pair.
typeInfer flag a@(Pair t1 t2) =
  do (ty1, ann1) <- typeInfer flag t1 
     (ty2, ann2) <- typeInfer flag t2
     return (Tensor ty1 ty2, Pair ann1 ann2)

typeInfer False a@(LamAnn ty (Abst xs m)) =
  do (_, tyAnn1) <- if isKind ty then typeCheck True ty Sort else typeCheck True ty Set
     let tyAnn'' = toEigen tyAnn1
     mapM_ (\ x -> addVar x (erasePos tyAnn'')) xs
     p <- isParam tyAnn''
     (ty', ann) <- typeInfer False m
     foldM (helper p tyAnn'') (ty', ann) xs
       where helper p tyAnn'' (ty', ann) x =
               if x `S.member` getVars AllowEigen ty'
               then
                 do removeVar x
                    return (Pi (abst [x] ty') tyAnn'', LamAnn tyAnn'' (abst [x] ann))
               else
                 do when (not p) $ checkUsage x m >> return ()
                    removeVar x
                    return (Arrow tyAnn'' ty', LamAnn tyAnn'' (abst [x] ann))

typeInfer flag (WithType a t) =
  do (_, tAnn1) <- typeCheck True t Set
     let tAnn' = erasePos (unEigen tAnn1)
     (_, ann) <- typeCheck False a tAnn' 
     let tAnn'' = toEigen tAnn'
     return (tAnn'', WithType ann tAnn'')


typeInfer flag a@(Case _ _) = freshNames ["#case"] $ \ [n] ->
  do (t, ann) <- typeCheck flag a (Var n)
     return (t, WithType ann t)

typeInfer flag a@(Let _ _) = freshNames ["#let"] $ \ [n] ->
  do (t, ann) <- typeCheck flag a (Var n)
     return (t, WithType ann t)

typeInfer flag a@(LetPair _ _) = freshNames ["#letPair"] $ \ [n] ->
  do (t, ann) <- typeCheck flag a (Var n)
     return (t, WithType ann t)

typeInfer flag a@(Lam _) = throwError $ LamInferErr a


typeInfer flag e = throwError $ Unhandle e



typeCheck flag (Pos p e) ty =
  do (ty', ann) <- typeCheck flag e ty `catchError` \ e -> throwError $ addErrPos p e
     return (ty', Pos p ann)

-- Sort check
typeCheck True Set Sort = return (Sort, Set)

typeCheck True (Arrow ty1 ty2) Sort =
  do (_, ty1') <- if isKind ty1 then typeCheck True ty1 Sort
                  else typeCheck True ty1 Set
     (_, ty2') <- typeCheck True ty2 Sort
     return (Sort, Arrow ty1' ty2')


typeCheck True (Pi (Abst xs m) ty) Sort = 
  do (_, ty') <- if isKind ty then typeCheck True ty Sort
            else typeCheck True ty Set
     mapM_ (\ x -> addVar x (erasePos ty')) xs
     let sub = zip xs (map EigenVar xs)
         m' = apply sub m
     (_, ann2) <- typeCheck True m' Sort
     let res = Pi (abst xs ann2) ty'
     mapM_ removeVar xs
     return (Sort, res)

-- Kind check
typeCheck True Unit Set = return (Set, Unit)

typeCheck True (Bang ty) Set =
  do (_, a) <- typeCheck True ty Set
     return (Set, Bang a)

typeCheck True (Arrow ty1 ty2) Set =
  do (_, ty1') <- if isKind ty1 
                  then typeCheck True ty1 Sort
                  else typeCheck True ty1 Set
     (_, ty2') <- typeCheck True ty2 Set
     return (Set, Arrow ty1' ty2')


typeCheck True (Imply tys ty2) Set =
  do res <- mapM (\ x -> typeCheck True x Set) tys
     let tys1 = map snd res
     mapM checkClass tys1
     updateParamInfo tys1
     updateSimpleInfo tys1
     (_, ty2') <- typeCheck True ty2 Set
     return (Set, Imply tys1 ty2')

typeCheck True (Tensor ty1 ty2) Set =
  do (_, ty1') <- typeCheck True ty1 Set
     (_, ty2') <- typeCheck True ty2 Set
     return (Set, Tensor ty1' ty2')
     
typeCheck True (Circ t u) Set =
  do (_, t') <- typeCheck True t Set
     (_, u') <- typeCheck True u Set
     return (Set, Circ t' u')

typeCheck True (Pi (Abst xs m) ty) Set = 
    do (_, tyAnn) <- if isKind ty then typeCheck True ty Sort else typeCheck True ty Set
       mapM_ (\ x -> addVar x (erasePos tyAnn)) xs
       let sub = zip xs (map EigenVar xs)
           m' = apply sub m
       (_, ann2) <- typeCheck True m' Set
       ann2' <- updateWithSubst ann2
       ann2'' <- resolveGoals ann2'
       let res = Pi (abst xs ann2'') tyAnn
       mapM_ removeVar xs
       return (Set, res)

typeCheck True pty@(PiImp (Abst xs m) ty) Set = 
  do   isP <- isParam ty
       when (not isP) $ throwError $ ForallLinearErr xs ty pty            
       (_, tyAnn) <- if isKind ty then typeCheck True ty Sort else typeCheck True ty Set
       mapM_ (\ x -> addVar x (erasePos tyAnn)) xs
       
       let sub = zip xs (map EigenVar xs)
           m' = apply sub m
       (_, ann2) <- typeCheck True m' Set
       ann2' <- updateWithSubst ann2
       ann2'' <- resolveGoals ann2'
       let res = PiImp (abst xs ann2'') tyAnn
       mapM_ removeVar xs
       return (Set, res)


typeCheck True (Forall (Abst xs m) ty) a@(Set) | isKind ty = 
  do (_, tyAnn) <- typeCheck True ty Sort
     mapM_ (\ x -> addVar x (erasePos tyAnn)) xs
     let sub = zip xs (map EigenVar xs)
         m' = apply sub m
     (_, ann) <- typeCheck True m' a
     ann' <- updateWithSubst ann
     ann'' <- resolveGoals ann'
     let res = Forall (abst xs ann'') tyAnn
     mapM_ (\ x -> removeVar x) xs
     return (a, res)

typeCheck True exp@(Forall (Abst xs m) ty) a@(Set) | otherwise = 
  do p <- isParam ty
     b <- getCheckBound
     when (not p && b) $ throwError (ForallLinearErr xs ty exp)
     (_, tyAnn) <- typeCheck True ty a
     mapM_ (\ x -> addVar x (erasePos tyAnn)) xs
     let sub = zip xs (map EigenVar xs)
         m' = apply sub m
     (_, ann) <- typeCheck True m' a
     ann' <- updateWithSubst ann
     ann'' <- resolveGoals ann'  
     let res = Forall (abst xs ann'') tyAnn
     mapM_ removeVar xs
     return (a, res)

typeCheck True (Exists (Abst xs m) ty) a@(Set) | not (isKind ty) = 
    do (_, ann1) <- typeCheck True ty a
       addVar xs (erasePos ann1)
       let sub = [(xs, EigenVar xs)]
           m' = apply sub m  
       (_, ann2) <- typeCheck True m' a
       ann2' <- updateWithSubst ann2
       ann2'' <- resolveGoals ann2'
       let res = Exists (abst xs ann2'') ann1
       removeVar xs
       return (a, res)

typeCheck True a@(Lam bind) t | isKind t =
  case t of
    Arrow t1 t2 -> 
      open bind $
      \ xs m -> 
        case xs of
          x:[] -> do
             addVar x t1
             (_, ann) <- typeCheck True m t2
             ann' <- updateWithSubst ann
             ann'' <- resolveGoals ann'
             let res = Lam' (abst [x] ann'') 
             removeVar x
             return (t, res)
          y:ys -> do
             addVar y t1
             (_, ann) <- typeCheck True (Lam (abst ys m)) t2
             ann' <- updateWithSubst ann
             ann'' <- resolveGoals ann'
             let res = Lam' (abst [y] ann'') 
             removeVar y
             return (t, res)
    b -> throwError $ KArrowErr a t


-- Type check
typeCheck flag a (Forall (Abst xs m) ty) =
  do let sub1 = zip xs (map EigenVar xs)
         m' = apply sub1 m
     mapM_ (\ x -> addVar x ty) xs
     (t, ann) <- typeCheck flag a m'
     mapM_ removeVar xs
     -- It is important to update the annotation with current
     -- substitution before rebinding xs, so that variables in xs does not get leaked
     -- into outer environment. Also, we will have to resolve all the constraint before
     -- going out of this forall environment.
     ann' <- updateWithSubst ann
     t' <- updateWithSubst t
     -- It is necessary to resolve all the goals before going out of
     -- the scope of xs as well.
     ann'' <- resolveGoals ann'
     mapM_ (checkExplicit ann'') xs
     let res = if isKind ty then (Forall (abst xs $ t') ty, LamType (abst xs $ ann''))
               else (Forall (abst xs $ t') ty, LamTm (abst xs $ ann''))
     return res
  where checkExplicit ann'' x =
          when (isExplicit x ann'') $ throwError $ ImplicitVarErr x ann''


typeCheck False (LamDict (Abst xs e)) (Imply bds ty) =
  let lxs = length xs
      lbd = length bds
  in if lxs <= lbd then
       do let (pre, post) = splitAt lxs bds
              ty' = if null post then ty else Imply post ty
          mapM (\ (x, y) -> addVar x y) (zip xs pre)
          (ty'', a) <- typeCheck False e ty'
          mapM_ removeVar xs
          return (Imply pre ty'', LamDict (abst xs a))
     else do let (pre, post) = splitAt lbd xs
             mapM (\ (x, y) -> addVar x y) (zip pre bds)
             (ty', a) <- typeCheck False (LamDict (abst post e)) ty
             mapM_ removeVar pre
             return (Imply bds ty', LamDict (abst pre a))
       

typeCheck flag a (Imply bds ty) =
  do let ns1 = take (length bds) (repeat "#inst")
     ns <- newNames ns1
     -- Note that we update the parameter variable information here.
     updateParamInfo bds
     updateSimpleInfo bds
     freshNames ns $ \ ns ->
       do bds' <- mapM normalize bds
          let instEnv = zip ns bds'
          mapM_ (\ (x, t) -> insertLocalInst x t) instEnv
          (t, ann) <- typeCheck flag a ty
          -- Make sure we use the hypothesis before going out of the scope of Imply.
          ann' <- resolveGoals ann
          mapM_ (\ (x, t) -> removeLocalInst x) instEnv
          let res = LamDict (abst ns ann') 
          return (Imply bds t, res)

typeCheck flag a (Bang ty) =
  do r <- isValue a
     if r then
       do checkParamCxt a
          (t, ann) <- typeCheck flag a ty
          case erasePos ann of
            Force ann' -> return (Bang t, ann')
            _ -> return (Bang t, Lift ann)
          
       else equality flag a (Bang ty)


typeCheck False c@(Lam bind) t =
  do at <- updateWithSubst t
     if not (at == t) then
       typeCheck False c at
       else
       case at of
         Arrow t1 t2 -> 
           open bind $
           \ xs m ->
             case xs of
               x:[] -> 
                 do addVar x t1 
                    (t2', ann) <- typeCheck False m t2
                    checkUsage x m 
                    removeVar x
                -- x cannot appear in type annotation, so we do not
                -- need to update the ann with current substitution.
                    let res = Lam (abst [x] ann)
                    return (Arrow t1 t2', res)
               y:ys -> 
                 do addVar y t1 
                    (t2', ann) <- typeCheck False (Lam (abst ys m)) t2
                    checkUsage y m 
                    removeVar y
                    let res = Lam (abst [y] ann)
                    return (Arrow t1 t2', res)
         Pi bd ty -> 
           open bind $ \ xs m -> open bd $ \ ys b ->
                   if length xs <= length ys then
                     do let sub1 = zip ys (map EigenVar xs)
                            b' = apply sub1 b
                            (vs, rs) = splitAt (length xs) ys
                            sub2 = zip xs (map EigenVar xs)
                            m' = apply sub2 m
                        mapM_ (\ x -> addVar x ty) xs
                        (t, ann) <- typeCheck False m'
                                    (if null rs then b' else Pi (abst rs b') ty)
                        mapM (\ x -> checkUsage x m') xs 
                        mapM_ removeVar xs
                        -- Since xs may appear in the type annotation in ann,
                        -- we have to update ann with current substitution.
                        -- before going out of the scope of xs. We also have to
                        -- resolve the current goals because current goals may
                        -- depend on xs.
                        ann2 <- updateWithSubst ann
                        ann' <- resolveGoals ann2
                        t' <- updateWithSubst t
                        let lamDep = if isKind ty then LamDepTy else LamDep
                            res = lamDep (abst xs ann') 
                            t'' = Pi (abst xs t') ty
                        return (t'', res)
                   else
                     do let lamDep = if isKind ty then LamDepTy else LamDep
                            sub1 = zip ys (map EigenVar xs)
                            b' = apply sub1 b
                            (vs, rs) = splitAt (length ys) xs
                            sub2 = zip xs $ take (length ys) (map EigenVar xs)
                            m' = apply sub2 m
                        mapM_ (\ x -> addVar x ty) vs
                        (t, ann) <- typeCheck False
                                    (if null rs then m' else Lam (abst rs m'))
                                    b'
                        mapM (\ x -> checkUsage x m') vs
                        mapM_ removeVar vs
                        ann1 <- updateWithSubst ann
                        t' <- updateWithSubst t
                        ann' <- resolveGoals ann1
                        let res = lamDep (abst vs ann') 
                        return (Pi (abst vs t') ty, res)
         pty@(PiImp bd ty) -> 
           open bind $ \ xs m -> open bd $ \ ys b ->
                   if length xs <= length ys then
                     do let sub1 = zip ys (map EigenVar xs)
                            b' = apply sub1 b
                            (vs, rs) = splitAt (length xs) ys
                            sub2 = zip xs (map EigenVar xs)
                            m' = apply sub2 m
                        mapM_ (\ x -> addVar x ty) xs
                        (t, ann) <- typeCheck False m'
                                    (if null rs then b' else PiImp (abst rs b') ty)
                        mapM_ removeVar xs
                        -- Since xs may appear in the type annotation in ann,
                        -- we have to update ann with current substitution.
                        -- before going out of the scope of xs. We also have to
                        -- resolve the current goals because current goals may
                        -- depend on xs.
                        ann2 <- updateWithSubst ann
                        ann' <- resolveGoals ann2
                        t' <- updateWithSubst t
                        let lamDep = if isKind ty then LamDepTy else LamDep
                            res = lamDep (abst xs ann') 
                            t'' = PiImp (abst xs t') ty
                        return (t'', res)
                   else
                     do let sub1 = zip ys (map EigenVar xs)
                            b' = apply sub1 b
                            (vs, rs) = splitAt (length ys) xs
                            sub2 = zip xs $ take (length ys) (map EigenVar xs)
                            m' = apply sub2 m
                        mapM_ (\ x -> addVar x ty) vs
                        (t, ann) <- typeCheck False
                                    (if null rs then m' else Lam (abst rs m'))
                                    b'
                        mapM_ removeVar vs
                        ann1 <- updateWithSubst ann
                        t' <- updateWithSubst t
                        ann' <- resolveGoals ann1
                        let lamDep = if isKind ty then LamDepTy else LamDep
                            res = LamDep (abst vs ann') 
                        return (PiImp (abst vs t') ty, res)
         b -> throwError $ LamErr c b

typeCheck flag a@(Pair t1 t2) (Exists p ty) =
  do (ty', ann1) <- typeCheck flag t1 ty
     open p $ \ x t ->
       do let vars = S.toList $ getVars NoEigen t1
              sub1 = zip vars (map EigenVar vars)
          t1Eigen <- shape $ apply sub1 ann1
          let t' = apply [(x, t1Eigen)] t
          (p', ann2) <- typeCheck flag t2 t'
          -- t' is an instance of t, it does not contain x anymore,
          -- hence the return type should be Exists p ty', not
          -- Exists (abst x p') ty'
          return (Exists p ty', Pair ann1 ann2)


typeCheck flag a@(Pair t1 t2) d =
  do sd <- updateWithSubst d
     ns <- newNames ["#unif", "#unif"]
     case erasePos sd of
       Tensor ty1 ty2 ->
         do (ty1', t1') <- typeCheck flag t1 ty1
            (ty2', t2') <- typeCheck flag t2 ty2
            return (Tensor ty1' ty2', Pair t1' t2')
       b -> freshNames ns $
            \ (x1:x2:[]) ->
              do let res = runUnify sd (Tensor (Var x1) (Var x2))
                 case res of
                   Just s ->
                     do ss <- getSubst
                        let sub' = s `mergeSub` ss
                        updateSubst sub'
                        let x1' = substitute sub' (Var x1)
                            x2' = substitute sub' (Var x2)
                        (x1'', t1') <- typeCheck flag t1 x1'
                        (x2'', t2') <- typeCheck flag t2 x2'
                        let res = Pair t1' t2'
                        return (Tensor x1'' x2'', res)
                   Nothing -> throwError (TensorExpErr a b)

typeCheck flag (Let m bd) goal =
  do (t', ann) <- typeInfer flag m
     open bd $ \ x t ->
           do let vs = S.toList $ getVars NoEigen ann
                  su = zip vs (map EigenVar vs)
              m'' <- shape $ apply su ann
              addVarDef x t' m'' 
              (goal', ann2) <- typeCheck flag t goal
              checkUsage x t
              -- If the goal resolution fails, delay it for upper level to resolve 
              ann2' <- (resolveGoals ann2 >>= updateWithSubst) `catchError`
                          \ e -> return ann2
              removeVar x
              let res = Let ann (abst x ann2') 
              return (goal', res)


typeCheck flag (LetPair m (Abst xs n)) goal =
  do (t', ann) <- typeInfer flag m
     at <- updateWithSubst t'
     case at of
       Exists (Abst x1 b') t1 ->
         do when (length xs /= 2) $ throwError $ ArityExistsErr at xs
            let (x:y:[]) = xs
                b = n
            addVar x t1
            addVar y (apply [(x1, EigenVar x)] b')
            let b'' = apply [(x, EigenVar x)] b
            (goal', ann2) <- typeCheck flag b'' goal
            ann2' <- updateWithSubst ann2
            ann3 <- resolveGoals ann2'
            checkUsage y b
            checkUsage x b
            removeVar x
            removeVar y
            let res = LetPair ann (abst [x, y] ann3) 
            return (goal', res)

       _ -> case unTensor (length xs) at of
         Just ts ->
           do let env = zip xs ts
              mapM (\ (x, t) -> addVar x t) env
              (goal', ann2) <- typeCheck flag n goal
              mapM (\ (x, t) -> checkUsage x n) env
              mapM removeVar xs
              ann2' <- updateWithSubst ann2
              let res = LetPair ann (abst xs ann2') 
              return (goal', res)
         Nothing ->
           do nss <- newNames $ map (\ x -> "#unif") xs
              freshNames nss $ \ (h:ns) ->
                  do let newTensor = foldl Tensor (Var h) (map Var ns)
                         vars = map Var (h:ns)
                     res <- normalizeUnif at newTensor
                     case res of
                       Nothing -> throwError $ TensorErr (length xs) m at
                       Just s ->
                         do ss <- getSubst
                            let sub' = s `mergeSub` ss
                            updateSubst sub'
                            let ts' = map (substitute sub') vars
                                env' = zip xs ts'
                            mapM (\ (x, t) -> addVar x t) env'
                            (goal', ann2) <- typeCheck flag n (substitute sub' goal)
                            mapM (\ x -> checkUsage x n) xs
                            mapM removeVar xs
                            ann2' <- updateWithSubst ann2
                            let res = LetPair ann (abst xs ann2') 
                            return (goal', res)

typeCheck flag (LetPat m bd) goal =
  do (tt, ann) <- typeInfer flag m
     ss <- getSubst
     let t' = substitute ss tt
     open bd $ \ (PApp kid vs) n ->
       do funPac <- lookupId kid
          let dt = classifier funPac
          (isSemi, index) <- isSemiSimple kid
          (head, axs, ins, kid', eigen) <- extendEnv vs dt (Const kid)
          inf <- getInfer
          let matchEigen = isEigenVar m
              isDpm = (isSemi || matchEigen) && not inf
              eSub = map (\ x -> (x, EigenVar x)) eigen
          unifRes <- patternUnif m isDpm index head t'
          case unifRes of
            Nothing ->
              throwError $ withPosition m (UnifErr head t') 
            Just sub' -> do
                 sub1 <- if matchEigen && not inf
                         then makeSub m sub' $
                              foldl (\ x (Right y) -> App x (EigenVar y)) kid' vs
                         else return sub'
                 let sub'' = sub1 `mergeSub` ss
                 updateSubst sub''
                 let goal' = substitute sub'' goal
                     n' = apply eSub n
                 (goal'', ann2) <- typeCheck flag n' goal'
                 subb <- getSubst
                 mapM (\ (Right v) -> checkUsage v n >>= \ r -> (return (v, r))) vs
                 mapM_ (\ (Right v) -> removeVar v) vs
                 -- It is important to update the environment before going
                 -- out of a dependent pattern matching
                 updateLocalInst subb
                 ann2' <- resolveGoals (substitute subb ann2)
                 -- !!!! Note that let pat is ok to leak local substitution,
                 -- as the branch is really global!.
                 -- when isDpm $ updateSubst ss
                 -- when (not isDpm) $ updateSubst subb
                 mapM removeLocalInst ins
                 let axs' = map (substVar subb) axs
                     goal''' = substitute subb goal''
                     res = LetPat ann (abst (PApp kid axs') ann2')
                 return (goal''', res)
     where
           makeSub (EigenVar x) s u =
             do  u' <- shape $ substitute s u
                 return $ Map.union s (Map.fromList [(x, u')])
           makeSub (Pos p x) s u = makeSub x s u
           makeSub a s u = return s
           
           substVar ss (Right x) =
             let r = substitute ss (Var x)
             in if r /= (Var x) then
                  Left (NoBind r)
                else Right x


typeCheck flag a@(Case tm (B brs)) goal =
  do (t, ann) <- typeInfer flag tm
     at <- updateWithSubst t
     let t' = flatten at
     when (t' == Nothing) $ throwError (DataErr at tm) 
     let Just (Right id, _) = t'
     updateCountWith (\ c -> enterCase c id)
     r <- checkBrs at brs goal
     let (_, brss) = unzip r
     updateCountWith exitCase
     let res = Case ann (B brss)
     return (goal, res)
  where makeSub (EigenVar x) s u =
          do u' <- shape $ substitute s u
             return $ s `Map.union` Map.fromList [(x, u')]
        makeSub (Pos p x) s u = makeSub x s u
        makeSub a s u = return s
        substVar ss (Right x) =
             let r = substitute ss (Var x)
             in if r /= (Var x) then
                  Left (NoBind r)
                else Right x
        
        checkBrs t pbs goal =
          mapM (checkBr t goal) pbs
          
        checkBr t goal pb =
          open pb $ \ p m ->
           case p of
             PApp kid vs ->
               do funPac <- lookupId kid
                  let dt = classifier funPac
                  updateCountWith (\ c -> nextCase c kid)
                  (isSemi, index) <- isSemiSimple kid
                  (head, axs, ins, kid', eigen) <- extendEnv vs dt (Const kid)
                  inf <- getInfer
                  let matchEigen = isEigenVar tm
                      eSub = map (\ x -> (x, EigenVar x)) eigen
                      -- infer mode over-write dependent pattern matching
                      isDpm = (isSemi || matchEigen) && not inf
                  ss <- getSubst
                  unifRes <- patternUnif tm isDpm index head t
                  case unifRes of
                    Nothing -> throwError $ withPosition tm (UnifErr head t) 
                    Just sub' -> do
                         sub1 <- if matchEigen && not inf then
                                      makeSub tm sub' $
                                      foldl (\ x (Right y) -> App x (EigenVar y)) kid' vs
                                 else return sub'
                         let sub'' = sub1 `mergeSub` ss
                         updateSubst sub''
                         -- We use special substitution for goal
                         let goal' = substitute sub'' goal
                             m' = apply eSub m
                         (goal'', ann2) <- typeCheck flag m' goal'
                         subb <- getSubst 
                         mapM (\ (Right v) -> checkUsage v m >>=
                                                          \ r -> return (v, r)) vs

                         updateLocalInst subb
                         
                         -- we need to restore the substitution to ss
                         -- because subb' may be influenced by dependent pattern matching.
                         let goal''' = substitute subb goal''
                         ann2' <- resolveGoals (substitute subb ann2) `catchError`
                                  \ e -> return ann2
                                  
                         when isDpm $ updateSubst ss
                         when (not isDpm) $ updateSubst subb
                         -- because the variable axs may be in the domain
                         -- of the substitution, hence it is necessary to update
                         -- axs as well before binding.
                         let axs' = map (substVar subb) axs
                         mapM_ (\ (Right v) -> removeVar v) vs
                         mapM removeLocalInst ins
                         return (goal''', abst (PApp kid axs') ann2')

typeCheck flag tm ty = equality flag tm ty


-- | Infer a type for tm, and check if it is unifiable with ty.
equality :: Bool -> Exp -> Exp -> TCMonad (Exp, Exp)
equality flag tm ty =
  do ty' <- updateWithSubst ty
     if not (ty == ty') then typeCheck flag tm ty'
       else
       do (tym, ann) <- typeInfer flag tm
          tym1 <- updateWithSubst tym
          ty1 <- updateWithSubst ty'
          -- Here we are assuming there is no types like !!A
          case (erasePos tym1, erasePos ty1) of
            (Bang tym1, Bang ty1) ->
              do (ty1, a2) <- handleEquality tm ann tym1 ty1
                 return (Bang ty1, a2)
            (tym1 , Bang ty1) -> throwError $ BangValue tm (Bang ty1)
            (tym1, ty1) -> handleEquality tm ann tym1 ty1
  where handleEquality tm ann tym1 ty1 = 
          do (a2, tym', anEnv) <- addAnn flag tm ann tym1 []
             mapM (\ (x, t) -> addVar x t) anEnv
             unifRes <- normalizeUnif tym' ty1
             case unifRes of
               Nothing -> 
                 -- do tyN1 <- normalize tym'
                 --    tyN2 <- normalize ty1
                 --    throwError $ NotEq tm tyN2 tyN1
                 throwError $ NotEq tm ty1 tym'
               Just s ->
                 do ss <- getSubst
                    let sub' = s `mergeSub` ss
                    updateSubst sub'
                    return (ty1, a2)




-- | Normalize and unify two expressions (head and t), taking
-- dependent pattern matching into account. Dependent pattern matching
-- has the effect of reverting eigenvariables into variables.
patternUnif :: Exp -> Bool -> Maybe Int -> Exp -> Exp -> TCMonad (Maybe (Map Variable Exp))
patternUnif m isDpm index head t =
  if isDpm then
    case index of
        Nothing -> normalizeUnif head t
        Just i ->
          case flatten t of
            Just (Right h, args) -> 
              let (bs, a:as) = splitAt i args
                  vars = S.toList $ getVars OnlyEigen a
                  eSub = zip vars (map EigenVar vars)
                  a' = unEigenBound vars a
                  t' = foldl App' (LBase h) (bs++(a':as))
              in do r <- normalizeUnif head t'
                    case r of
                      Nothing -> return Nothing
                      Just subst ->
                        helper subst vars eSub
            _ -> throwError $ withPosition m (UnifErr head t)
  else normalizeUnif head t
  where -- change relavent variables back into eigenvariables after dependent pattern-matching 
        helper subst (v:vars) eSub =
          let subst' = Map.mapWithKey (\ k val -> if k == v then toEigen val else val) subst
              subst'' = Map.map (\ val -> apply eSub val) subst'
          in helper subst'' vars eSub
        helper subst [] eSub = return $ Just subst
          
      
-- | Normalize two expressions and then unify them.  
-- There is a degree of freedom in implementing normalizeUnif function. It could be
-- further improved.
normalizeUnif :: Exp -> Exp -> TCMonad (Maybe (Map Variable Exp))
normalizeUnif t1 t2 =
 do t1' <- resolveGoals t1
    t2' <- resolveGoals t2
    case runUnify t1' t2' of
      Just s -> return $ Just s
      Nothing -> 
        case (flatten t1', flatten t2') of
          (Just (Right f1, args1), Just (Right f2, args2)) 
            | (f1 == f2) && (length args1 == length args2) ->
              foldM (\ s (x, y) ->
                case s of
                  Nothing -> return Nothing
                  Just s1 ->
                    let x' = substitute s1 x
                        y' = substitute s1 y in
                    do r <- normalizeUnif x' y'
                       case r of
                         Nothing -> return Nothing
                         Just s2 -> return $ Just (mergeSub s2 s1)
                ) (Just Map.empty) (zip args1 args2)
            | otherwise -> return Nothing
          (_, _) -> 
            do t1'' <- normalize t1'
               t2'' <- normalize t2'
               return $ runUnify t1'' t2''


-- | Extend the typing environment with
-- the environment induced by pattern. Its first argument is the list from 'Pattern'.
-- Its second argument is the type of the constructor, its third argument is the constructor
-- of the pattern. It will return the following, Exp: head of the type expression,
-- [Either a Variable]: essentially an extended list of pattern variables,
-- [Variable]: a list of dictionary variables, Exp: annotated version of the constructor,
-- [Variable]: a list of eigenvariables.

extendEnv :: [Either (NoBind Exp) Variable] -> Exp -> Exp ->
             TCMonad (Exp, [Either a Variable], [Variable], Exp, [Variable])
extendEnv xs (Forall bind ty) kid | isKind ty =
  open bind $
      \ ys t' ->
      do mapM_ (\ x -> addVar x ty) ys
         let kid' = foldl AppType kid (map Var ys)
         (h, vs, ins, kid'', eigen) <- extendEnv xs t' kid'
         let vs' = map Right ys ++ vs
         return (h, vs', ins, kid'', eigen)

extendEnv xs (Forall bind ty) kid | otherwise =
  open bind $
      \ ys t' ->
      do mapM_ (\ x -> addVar x ty) ys
         let kid' = foldl AppTm kid (map Var ys)
         (h, vs, ins, kid'', eigen) <- extendEnv xs t' kid'
         let vs' = (map Right ys)++vs
         return (h, vs', ins, kid'', eigen)

extendEnv xs (Imply bds ty) kid =
  do let ns1 = take (length bds) (repeat "#inst")
     ns <- newNames ns1
     freshNames ns $ \ ns ->
       do mapM_ (\ (x, y) -> insertLocalInst x y) (zip ns bds)
          let kid' = foldl AppDict kid (map Var ns)
          (h, vs, ins, kid'', eigen) <- extendEnv xs ty kid'
          return (h, (map Right ns)++vs, ns++ins, kid'', eigen)

extendEnv [] t kid = return (t, [], [], kid, [])

extendEnv (Right x:xs) (Arrow t1 t2) kid =
  do addVar x t1
     (h, ys, ins, kid', eigen) <- extendEnv xs t2 kid
     return (h,  Right x : ys, ins, kid', eigen)

extendEnv (Right x : xs) (Pi bind ty) kid
  | not (isKind ty) =
    open bind $ \ ys t' ->
    do let y = head ys
           t'' = apply [(y , EigenVar x)] t'  -- note that Pi is existential
       addVar x ty
       if null (tail ys)
         then do (h, ys, ins, kid', eigen) <- extendEnv xs t'' kid
                 return (h, (Right x : ys), ins, kid', x:eigen)
         else do (h, ys, ins, kid', eigen) <- extendEnv xs (Pi (abst (tail ys) t'') ty) kid
                 return (h, (Right x : ys), ins, kid', x:eigen)

     
extendEnv a b kid = throwError $ ExtendEnvErr a b


-- | Infer a type for a type application.
handleTypeApp :: Exp -> Exp -> Exp -> Exp -> TCMonad (Exp, Exp)
handleTypeApp ann t' t1 t2 =
  case erasePos t' of
    Arrow k1 k2 ->
        do (_, ann2) <- typeCheck True t2 k1
           return (k2, App' ann ann2)
    Pi b ty ->
      open b $ \ vs b' ->
        do (_, ann2) <- typeCheck True t2 ty
           let t2' = erasePos $ toEigen ann2
           b'' <- betaNormalize (apply [(head vs, t2')]  b')
           let k2 = if null (tail vs) then b''
                      else Pi (abst (tail vs) b'') ty
           return (k2, App' ann ann2)
           
    a -> throwError $ KAppErr t1 (App t1 t2) a  

-- | Infer a type for a term application.
handleTermApp :: Bool -> Exp -> Exp -> Exp -> Exp -> Exp -> TCMonad (Exp, Exp)
handleTermApp flag ann pos t' t1 t2 = 
  do (a1', rt, anEnv) <- addAnn flag pos ann t' []
     mapM (\ (x, t) -> addVar x t) anEnv
     rt' <- updateWithSubst rt
     case rt' of
       Arrow ty1 ty2 | isKind ty1 ->
         do (_, ann2) <- typeCheck True t2 ty1
            let res = AppDepTy a1' ann2
            return (ty2, res)
       Arrow ty1 ty2 ->
         do (_, ann2) <- typeCheck flag t2 ty1
            let res = if flag then App' a1' ann2 else App a1' ann2
            return (ty2, res)
       Arrow' ty1 ty2 ->
         do (_, ann2) <- typeCheck True t2 ty1
            let res = App' a1' ann2
            return (ty2, res)            
       b@(Pi bind ty) ->
         open bind $
         \ xs m -> 
                -- typecheck or kind check t2
                -- since t2 may travels to m, we
                -- normalize [[t2]/x]m
             do let flag' = isKind ty
                (_, kann) <- typeCheck flag' t2 ty
                let t2' = erasePos $ toEigen kann
                t2'' <- if not flag' then shape t2' else return t2'
                m' <- betaNormalize (apply [(head xs, t2'')] m)
                let res =
                      case (flag, flag') of
                        (False, False) -> AppDep a1' kann
                        (False, True) -> AppDepTy a1' kann
                        (True, False) -> AppDep' a1' kann
                        (True, True) -> AppDepTy a1' kann
                if null (tail xs)
                  then
                  do m'' <- updateWithSubst m'
                     res' <- updateWithSubst res
                     return (m'', res')
                  else
                  do m'' <- updateWithSubst m'
                     ty' <- updateWithSubst ty
                     res' <- updateWithSubst res
                     return (Pi (abst (tail xs) m'') ty', res')
                     
       b -> throwError $ ArrowErr t1 b


-- | Add annotations to the term /a/ according to its type if it is applied to some
-- other terms.
addAnn :: Bool -> Exp -> Exp -> Exp -> [(Variable, Exp)] -> TCMonad (Exp, Exp, [(Variable, Exp)])
addAnn flag e a (Pos _ t) env = addAnn flag e a t env

addAnn flag e a (Bang t) env =
  do let force = if flag then Force' else Force
     t' <- if flag then shape t else return t
     addAnn flag e (force a) t' env

addAnn flag e a (Forall bd ty) env | isKind ty = open bd $ \ xs t ->
       let a' = foldl AppType a (map Var xs)
           new = map (\ x -> (x, ty)) xs
       in addAnn flag e a' t (new ++ env)

addAnn flag e a (Forall bd ty) env | otherwise = open bd $ \ xs t ->
       let a' = foldl AppTm a (map Var xs)
           new = map (\ x -> (x, ty)) xs
       in addAnn flag e a' t (new ++ env)

addAnn flag e a (PiImp bd ty) env | isKind ty = open bd $ \ xs t ->
       let a' = foldl AppDepTy a (map Var xs)
           new = map (\ x -> (x, ty)) xs
       in addAnn flag e a' t (new ++ env)          

addAnn flag e a (PiImp bd ty) env | otherwise = open bd $ \ xs t ->
       let app = if flag then AppDep' else AppDep
           a' = foldl app a (map Var xs)
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

