{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
-- | This module implements a bi-directional algorithm for elaborating
-- the surface language into the core language. The elaborated programs
-- will be checked by the "Proofchecking" module. The elaboration aims for soundness, i.e.,
-- if the elaboration is successful, then it shoud past the proof-checker. Otherwise it
-- means there is a bug in the elaboration. 


module Typechecking (typeCheck, typeInfer) where

import Syntax
import SyntacticOperations
import TCMonad
import TypeError
import Utils
import Normalize
import Substitution
import TypeClass
import Unification
import ModeResolve

import Nominal
import qualified Data.Set as S
import qualified Data.Map as Map
import Data.Map (Map)
import Debug.Trace
import Control.Monad.Except
import Control.Monad.State
import Text.PrettyPrint
import Prelude hiding((<>))

-- | Check an expression against a type, retun elaborated term and type.
-- The flag = True indicates
-- it is during kinding or sorting, flag = False indicates it is during type checking.
-- For simplicity, we do not allow direct mentioning
-- of lambda, box, unbox, reverse, runCirc, existsBox in types (these will give rise to
-- type errors saying no typing rule for inference). 

typeCheck :: Bool -> Modality -> Exp -> Exp -> TCMonad (Exp, Exp, Modality)

-- | Infer a type for a term, also return elaborated term.
typeInfer :: Bool -> Modality -> Exp -> TCMonad (Exp, Exp, Modality)

typeInfer flag m (Pos p e) =
  do (ty, ann, m') <- typeInfer flag m e `catchError` \ e -> throwError $ addErrPos p e
     return (ty, (Pos p ann), m')

typeInfer True m Set = return (Sort, Set, m)

typeInfer True m a@(Base kid) =
  lookupId kid >>= \ x -> return (classifier x, a, m)

typeInfer True m a@(LBase kid) =
  lookupId kid >>= \ x -> return (classifier x, a, m)

typeInfer flag m a@(Var x) =
  do (t, _) <- lookupVar x
     if flag then
       do t' <- shape t 
          return (t', a, m)
       else
       do updateCount x
          return (t, a, m)

typeInfer flag m a@(EigenVar x) =
  do (t, _) <- lookupVar x
     if flag then
       do t' <- shape t 
          return (t', a, m)
       else
       do updateCount x
          return (t, a, m)
     
typeInfer flag m a@(Const kid) =
  do funPac <- lookupId kid
     let cl = classifier funPac
     case cl of
       Mod (Abst _ cl') -> 
         return (cl', a, m)
       _ -> return (cl, a, m)
         

typeInfer flag m a@(App t1 t2) =
  do (t', ann, m') <- typeInfer flag m t1
     if isKind t'
       then handleTypeApp ann t' t1 t2 m
       else handleTermApp flag ann t1 t' t1 t2 m m'

typeInfer False m a@(UnBox) =
  freshNames ["a", "b", "alpha", "beta"] $ \ [a, b, alpha, beta] ->
  let va = Var a
      vb = Var b
      simpClass = Id "Simple"
      boxMode = M (BConst True) (BVar alpha) (BVar beta)
      t1 = Arrow (Circ va vb boxMode) (Bang (Arrow va vb) boxMode)
      t1' = Imply [App' (Base simpClass) va , App' (Base simpClass) vb] t1
      ty = Forall (abst [a, b] t1') Set
      ty' = abstractMode ty
  in return (ty', UnBox, m)

typeInfer False mode a@(Reverse) =
  freshNames ["a", "b", "alpha"] $ \ [a, b, alpha] ->
  let va = Var a
      vb = Var b
      simpClass = Id "Simple"
      boxMode = M (BConst True) (BVar alpha) (BConst True)
      t1 = Arrow (Circ va vb boxMode) (Circ vb va boxMode)
      t1' = Imply [App' (Base simpClass) va , App' (Base simpClass) vb] t1
      ty = Forall (abst [a, b] t1') Set
      ty' = abstractMode ty
  in return (ty', Reverse, mode)

typeInfer False mode t@(Box) = freshNames ["a", "b", "alpha", "beta"] $ \ [a, b, alpha, beta] ->
  do let va = Var a
         vb = Var b
         simpClass = Id "Simple"
         boxMode = M (BConst True) (BVar alpha) (BVar beta)
         t1 = Arrow (Bang (Arrow va vb) boxMode) (Circ va vb boxMode)
         t1' = Imply [App' (Base simpClass) va , App' (Base simpClass) vb] t1
         boxType = Pi (abst [a] (Forall (abst [b] t1') Set)) Set
         ty' = abstractMode boxType
     return (ty', t, mode)

typeInfer False mode t@(RunCirc) =
  freshNames ["a", "b", "c", "d", "alpha", "beta"] $ \ [a, b, c, d, alpha, beta] ->
  do let va = Var a
         vb = Var b
         vc = Var c
         vd = Var d
         simpParam = Id "SimpParam"
         boxMode = M (BConst True) (BVar alpha) (BVar beta)
         t1 = Arrow (Circ va vb boxMode) (Arrow vc vd)
         t1' = Imply [App' (App' (Base simpParam) va) vc , App' (App' (Base simpParam) vb) vd] t1
         res = Forall (abst [a, b, c, d] t1') Set
         ty' = abstractMode res
     return (ty', t, mode)

typeInfer False mode t@(ExBox) =
  freshNames ["a", "b", "p", "n", "alpha", "beta"] $ \ [a, b, p, n, alpha, beta] ->
  do let va = Var a
         vb = Var b
         vp = Var p
         vn = Var n
         simpClass = Id "Simple"
         paramClass = Id "Parameter"
         kp = Arrow vb Set
         boxMode = M (BConst True) (BVar alpha) (BVar beta)
         simpA = App' (Base simpClass) va
         paramB = App' (Base paramClass) vb
         simpP = App' (Base simpClass) (App' vp vn)
         t1Output = Exists (abst n (App' vp vn)) vb
         t1 = Bang (Arrow va t1Output) boxMode
         output = Exists (abst n $ Imply [simpP] (Circ va (App' vp vn) boxMode)) vb
         beforePi = Arrow t1 output
         r = Pi (abst [a] $
                 Forall (abst [b] (Imply [simpA, paramB] $ Pi (abst [p] $ beforePi) kp)) Set) Set
         r' = abstractMode r
     return (r', t, mode)

typeInfer flag mode Star = return (Unit, Star, mode)
typeInfer flag mode Unit = return (Set, Unit, mode)

-- Only infering tensor product for pair.
typeInfer flag mode a@(Pair t1 t2) =
  do (ty1, ann1, mode1) <- typeInfer flag mode t1 
     (ty2, ann2, mode2) <- typeInfer flag mode t2
     return (Tensor ty1 ty2, Pair ann1 ann2, modalAnd mode1 mode2)

typeInfer False mode a@(LamAnn ty (Abst xs m)) =
  do (_, tyAnn1, _) <- if isKind ty then typeCheck True mode ty Sort
                       else typeCheck True mode ty Set
     let tyAnn'' = toEigen tyAnn1
     mapM_ (\ x -> addVar x (erasePos tyAnn'')) xs
     p <- isParam tyAnn''
     (ty', ann, mode') <- typeInfer False mode m
     foldM (helper p tyAnn'') (ty', ann, mode') xs
       where helper p tyAnn'' (ty', ann, mode') x =
               if x `S.member` getVars AllowEigen ty'
               then
                 do removeVar x
                    return (Pi (abst [x] ty') tyAnn'', LamAnn tyAnn'' (abst [x] ann), mode')
               else
                 do when (not p) $ checkUsage x m >> return ()
                    removeVar x
                    return (Arrow tyAnn'' ty', LamAnn tyAnn'' (abst [x] ann), mode')

typeInfer flag mode (WithType a t) =
  do (_, tAnn1, _) <- typeCheck True mode t Set
     let tAnn' = erasePos (unEigen tAnn1)
     (tAnn2, ann, mode') <- typeCheck False mode a tAnn' 
     let tAnn'' = toEigen tAnn2
     return (tAnn'', WithType ann tAnn'', mode')


typeInfer flag mode a@(Case _ _) = freshNames ["#case"] $ \ [n] ->
  do (t, ann, mode') <- typeCheck flag mode a (Var n)
     return (t, WithType ann t, mode')

typeInfer flag mode a@(Let _ _) = freshNames ["#let"] $ \ [n] ->
  do (t, ann, mode') <- typeCheck flag mode a (Var n)
     return (t, WithType ann t, mode')

typeInfer flag mode a@(LetPair _ _) = freshNames ["#letPair"] $ \ [n] ->
  do (t, ann, mode') <- typeCheck flag mode a (Var n)
     return (t, WithType ann t, mode')

typeInfer flag _ a@(Lam _) = throwError $ LamInferErr a


typeInfer flag _ e = throwError $ Unhandle e



typeCheck flag mode (Pos p e) ty =
  do (ty', ann, mode') <- typeCheck flag mode e ty `catchError` \ e -> throwError $ addErrPos p e
     return (ty', Pos p ann, mode')

-- using fresh modality variables.
typeCheck flag mode (Mod (Abst _ e)) ty = typeCheck flag mode e ty

-- Sort check
typeCheck True mode Set Sort = return (Sort, Set, mode)

typeCheck True mode (Arrow ty1 ty2) Sort =
  do (_, ty1', _) <- if isKind ty1 then typeCheck True mode ty1 Sort
                  else typeCheck True mode ty1 Set
     (_, ty2', _) <- typeCheck True mode ty2 Sort
     return (Sort, Arrow ty1' ty2', mode)


typeCheck True mode (Pi (Abst xs m) ty) Sort = 
  do (_, ty', _) <- if isKind ty then typeCheck True mode ty Sort
            else typeCheck True mode ty Set
     mapM_ (\ x -> addVar x (erasePos ty')) xs
     let sub = zip xs (map EigenVar xs)
         m' = apply sub m
     (_, ann2, _) <- typeCheck True mode m' Sort
     let res = Pi (abst xs ann2) ty'
     mapM_ removeVar xs
     return (Sort, res, mode)

-- Kind check
typeCheck True mode Unit Set = return (Set, Unit, mode)

typeCheck True mode (Bang ty m) Set =
  do (_, a, _) <- typeCheck True mode ty Set
     return (Set, Bang a m, mode)

typeCheck True mode (Arrow ty1 ty2) Set =
  do (_, ty1', _) <- if isKind ty1 
                  then typeCheck True mode ty1 Sort
                  else typeCheck True mode ty1 Set
     (_, ty2', _) <- typeCheck True mode ty2 Set
     return (Set, Arrow ty1' ty2', mode)


typeCheck True mode (Imply tys ty2) Set =
  do res <- mapM (\ x -> typeCheck True mode x Set) tys
     let tys1 = map (\ (x, y, z) -> y) res
     mapM checkClass tys1
     updateParamInfo tys1
     updateSimpleInfo tys1
     (_, ty2', _) <- typeCheck True mode ty2 Set
     return (Set, Imply tys1 ty2', mode)

typeCheck True mode (Tensor ty1 ty2) Set =
  do (_, ty1', _) <- typeCheck True mode ty1 Set
     (_, ty2', _) <- typeCheck True mode ty2 Set
     return (Set, Tensor ty1' ty2', mode)
     
typeCheck True mode (Circ t u m) Set =
  do (_, t', _) <- typeCheck True mode t Set
     (_, u', _) <- typeCheck True mode u Set
     return (Set, Circ t' u' m, mode)

typeCheck True mode (Pi (Abst xs m) ty) Set = 
    do (_, tyAnn, _) <- if isKind ty then typeCheck True mode ty Sort
                     else typeCheck True mode ty Set
       mapM_ (\ x -> addVar x (erasePos tyAnn)) xs
       let sub = zip xs (map EigenVar xs)
           m' = apply sub m
       (_, ann2, _) <- typeCheck True mode m' Set
       ann2' <- updateWithSubst ann2
       ann2'' <- resolveGoals ann2'
       let res = Pi (abst xs ann2'') tyAnn
       mapM_ removeVar xs
       return (Set, res, mode)

typeCheck True mode pty@(PiImp (Abst xs m) ty) Set = 
  do   isP <- isParam ty
       when (not isP) $ throwError $ ForallLinearErr xs ty pty            
       (_, tyAnn, _) <- if isKind ty then typeCheck True mode ty Sort
                     else typeCheck True mode ty Set
       mapM_ (\ x -> addVar x (erasePos tyAnn)) xs
       
       let sub = zip xs (map EigenVar xs)
           m' = apply sub m
       (_, ann2, _) <- typeCheck True mode m' Set
       ann2' <- updateWithSubst ann2
       ann2'' <- resolveGoals ann2'
       let res = PiImp (abst xs ann2'') tyAnn
       mapM_ removeVar xs
       return (Set, res, mode)


typeCheck True mode (Forall (Abst xs m) ty) a@(Set) | isKind ty = 
  do (_, tyAnn, _) <- typeCheck True mode ty Sort
     mapM_ (\ x -> addVar x (erasePos tyAnn)) xs
     let sub = zip xs (map EigenVar xs)
         m' = apply sub m
     (_, ann, mode) <- typeCheck True mode m' a
     ann' <- updateWithSubst ann
     ann'' <- resolveGoals ann'
     let res = Forall (abst xs ann'') tyAnn
     mapM_ (\ x -> removeVar x) xs
     return (a, res, mode)

typeCheck True mode exp@(Forall (Abst xs m) ty) a@(Set) | otherwise = 
  do p <- isParam ty
     b <- getCheckBound
     when (not p && b) $ throwError (ForallLinearErr xs ty exp)
     (_, tyAnn, _) <- typeCheck True mode ty a
     mapM_ (\ x -> addVar x (erasePos tyAnn)) xs
     let sub = zip xs (map EigenVar xs)
         m' = apply sub m
     (_, ann, _) <- typeCheck True mode m' a
     ann' <- updateWithSubst ann
     ann'' <- resolveGoals ann'  
     let res = Forall (abst xs ann'') tyAnn
     mapM_ removeVar xs
     return (a, res, mode)

typeCheck True mode (Exists (Abst xs m) ty) a@(Set) | not (isKind ty) = 
    do (_, ann1, _) <- typeCheck True mode ty a
       addVar xs (erasePos ann1)
       let sub = [(xs, EigenVar xs)]
           m' = apply sub m  
       (_, ann2, _) <- typeCheck True mode m' a
       ann2' <- updateWithSubst ann2
       ann2'' <- resolveGoals ann2'
       let res = Exists (abst xs ann2'') ann1
       removeVar xs
       return (a, res, mode)

typeCheck True mode a@(Lam bind) t | isKind t =
  case t of
    Arrow t1 t2 -> 
      open bind $
      \ xs m -> 
        case xs of
          x:[] -> do
             addVar x t1
             (_, ann, _) <- typeCheck True mode m t2
             ann' <- updateWithSubst ann
             ann'' <- resolveGoals ann'
             let res = Lam' (abst [x] ann'') 
             removeVar x
             return (t, res, mode)
          y:ys -> do
             addVar y t1
             (_, ann, _) <- typeCheck True mode (Lam (abst ys m)) t2
             ann' <- updateWithSubst ann
             ann'' <- resolveGoals ann'
             let res = Lam' (abst [y] ann'') 
             removeVar y
             return (t, res, mode)
    b -> throwError $ KArrowErr a t


-- Type check
typeCheck flag mode a (Forall (Abst xs m) ty) =
  do let sub1 = zip xs (map EigenVar xs)
         m' = apply sub1 m
     mapM_ (\ x -> addVar x ty) xs
     (t, ann, mode') <- typeCheck flag mode a m'
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
     let res = if isKind ty then (Forall (abst xs $ t') ty, LamType (abst xs $ ann''), mode')
               else (Forall (abst xs $ t') ty, LamTm (abst xs $ ann''), mode')
     return res
  where checkExplicit ann'' x =
          when (isExplicit x ann'') $ throwError $ ImplicitVarErr x ann''


typeCheck False mode (LamDict (Abst xs e)) (Imply bds ty) =
  let lxs = length xs
      lbd = length bds
  in if lxs <= lbd then
       do let (pre, post) = splitAt lxs bds
              ty' = if null post then ty else Imply post ty
          mapM (\ (x, y) -> addVar x y) (zip xs pre)
          (ty'', a, mode') <- typeCheck False mode e ty'
          mapM_ removeVar xs
          return (Imply pre ty'', LamDict (abst xs a), mode')
     else do let (pre, post) = splitAt lbd xs
             mapM (\ (x, y) -> addVar x y) (zip pre bds)
             (ty', a, mode') <- typeCheck False mode (LamDict (abst post e)) ty
             mapM_ removeVar pre
             return (Imply bds ty', LamDict (abst pre a), mode')
       

typeCheck flag mode a (Imply bds ty) =
  do let ns1 = take (length bds) (repeat "#inst")
     ns <- newNames ns1
     -- Note that we update the parameter variable information here.
     updateParamInfo bds
     updateSimpleInfo bds
     freshNames ns $ \ ns ->
       do bds' <- mapM normalize bds
          let instEnv = zip ns bds'
          mapM_ (\ (x, t) -> insertLocalInst x t) instEnv
          (t, ann, mode') <- typeCheck flag mode a ty
          -- Make sure we use the hypothesis before going out of the scope of Imply.
          ann' <- resolveGoals ann
          mapM_ (\ (x, t) -> removeLocalInst x) instEnv
          let res = LamDict (abst ns ann') 
          return (Imply bds t, res, mode')


typeCheck flag mode a@(Var x) (Bang ty m) =
  equality flag mode a (Bang ty m)

typeCheck flag mode a@(EigenVar x) (Bang ty m) =
  equality flag mode a (Bang ty m)

typeCheck flag mode a@(Const x) (Bang ty m) =
  do (ty1, _, mode') <- typeInfer flag mode a
     case ty1 of
       Bang _ _ -> 
         equality flag mode' a (Bang ty m)
       _ ->  
         do (t, ann, cMode) <- typeCheck flag mode' a ty
            let s = modeResolution cMode m
            when (s == Nothing) $ throwError $ ModalityErr cMode m a
            let Just s'@(s1, s2, s3) = s
                -- m' = modeSubst s' cMode
            updateModeSubst s'
            m' <- updateModality cMode
            return (Bang t (simplify m'), Lift ann, DummyM)
  
typeCheck flag cMode a (Bang ty m) =
  do r <- isValue a
     if r then
       do checkParamCxt a
          (t, ann, cMode') <- typeCheck flag cMode a ty
          let s = modeResolution cMode' m
          when (s == Nothing) $ throwError $ ModalityErr cMode' m a
          let Just s'@(s1, s2, s3) = s
          updateModeSubst s'
          m'' <- updateModality cMode'
          -- m''' <- updateModality m
          return (Bang t (simplify m''), Lift ann, DummyM)
       else throwError $ BangValue a (Bang ty m)


typeCheck False mode c@(Lam bind) t =
  do at <- updateWithSubst t
     if not (at == t) then
       typeCheck False mode c at
       else
       case at of
         Arrow t1 t2 -> 
           open bind $
           \ xs m ->
             case xs of
               x:[] -> 
                 do addVar x t1 
                    (t2', ann, mode') <- typeCheck False mode m t2
                    checkUsage x m 
                    removeVar x
                -- x cannot appear in type annotation, so we do not
                -- need to update the ann with current substitution.
                    let res = Lam (abst [x] ann)
                    return (Arrow t1 t2', res, mode')
               y:ys -> 
                 do addVar y t1 
                    (t2', ann, mode') <- typeCheck False mode (Lam (abst ys m)) t2
                    checkUsage y m 
                    removeVar y
                    let res = Lam (abst [y] ann)
                    return (Arrow t1 t2', res, mode')
         Pi bd ty -> 
           open bind $ \ xs m -> open bd $ \ ys b ->
                   if length xs <= length ys then
                     do let sub1 = zip ys (map EigenVar xs)
                            b' = apply sub1 b
                            (vs, rs) = splitAt (length xs) ys
                            sub2 = zip xs (map EigenVar xs)
                            m' = apply sub2 m
                        mapM_ (\ x -> addVar x ty) xs
                        (t, ann, mode') <- typeCheck False mode m'
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
                        return (t'', res, mode')
                   else
                     do let lamDep = if isKind ty then LamDepTy else LamDep
                            sub1 = zip ys (map EigenVar xs)
                            b' = apply sub1 b
                            (vs, rs) = splitAt (length ys) xs
                            sub2 = zip xs $ take (length ys) (map EigenVar xs)
                            m' = apply sub2 m
                        mapM_ (\ x -> addVar x ty) vs
                        (t, ann, mode') <- typeCheck False mode
                                    (if null rs then m' else Lam (abst rs m'))
                                    b'
                        mapM (\ x -> checkUsage x m') vs
                        mapM_ removeVar vs
                        ann1 <- updateWithSubst ann
                        t' <- updateWithSubst t
                        ann' <- resolveGoals ann1
                        let res = lamDep (abst vs ann') 
                        return (Pi (abst vs t') ty, res, mode')
         pty@(PiImp bd ty) -> 
           open bind $ \ xs m -> open bd $ \ ys b ->
                   if length xs <= length ys then
                     do let sub1 = zip ys (map EigenVar xs)
                            b' = apply sub1 b
                            (vs, rs) = splitAt (length xs) ys
                            sub2 = zip xs (map EigenVar xs)
                            m' = apply sub2 m
                        mapM_ (\ x -> addVar x ty) xs
                        (t, ann, mode') <- typeCheck False mode m'
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
                        return (t'', res, mode')
                   else
                     do let sub1 = zip ys (map EigenVar xs)
                            b' = apply sub1 b
                            (vs, rs) = splitAt (length ys) xs
                            sub2 = zip xs $ take (length ys) (map EigenVar xs)
                            m' = apply sub2 m
                        mapM_ (\ x -> addVar x ty) vs
                        (t, ann, mode') <- typeCheck False mode
                                    (if null rs then m' else Lam (abst rs m'))
                                    b'
                        mapM_ removeVar vs
                        ann1 <- updateWithSubst ann
                        t' <- updateWithSubst t
                        ann' <- resolveGoals ann1
                        let lamDep = if isKind ty then LamDepTy else LamDep
                            res = LamDep (abst vs ann') 
                        return (PiImp (abst vs t') ty, res, mode')
         b -> throwError $ LamErr c b

typeCheck flag mode a@(Pair t1 t2) (Exists p ty) =
  do (ty', ann1, mode1) <- typeCheck flag mode t1 ty
     open p $ \ x t ->
       do let vars = S.toList $ getVars NoEigen t1
              sub1 = zip vars (map EigenVar vars)
          t1Eigen <- shape $ apply sub1 ann1
          let t' = apply [(x, t1Eigen)] t
          (p', ann2, mode2) <- typeCheck flag mode t2 t'
          -- t' is an instance of t, it does not contain x anymore,
          -- hence the return type should be Exists p ty', not
          -- Exists (abst x p') ty'
          return (Exists p ty', Pair ann1 ann2, modalAnd mode1 mode2)


typeCheck flag mode a@(Pair t1 t2) d =
  do sd <- updateWithSubst d
     ns <- newNames ["#unif", "#unif"]
     case erasePos sd of
       Tensor ty1 ty2 ->
         do (ty1', t1', mode1) <- typeCheck flag mode t1 ty1
            (ty2', t2', mode2) <- typeCheck flag mode t2 ty2
            return (Tensor ty1' ty2', Pair t1' t2', modalAnd mode1 mode2)
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
                        (x1'', t1', mode1) <- typeCheck flag mode t1 x1'
                        (x2'', t2', mode2) <- typeCheck flag mode t2 x2'
                        let res = Pair t1' t2'
                        return (Tensor x1'' x2'', res, modalAnd mode1 mode2)
                   Nothing -> throwError (TensorExpErr a b)

typeCheck flag mode (Let m bd) goal =
  do (t', ann, mode') <- typeInfer flag mode m
     open bd $ \ x t ->
           do let vs = S.toList $ getVars NoEigen ann
                  su = zip vs (map EigenVar vs)
              m'' <- shape $ apply su ann
              addVarDef x t' m'' 
              (goal', ann2, mode'') <- typeCheck flag mode t goal
              checkUsage x t
              -- If the goal resolution fails, delay it for upper level to resolve 
              ann2' <- (resolveGoals ann2 >>= updateWithSubst) `catchError`
                          \ e -> return ann2
              removeVar x
              let res = Let ann (abst x ann2') 
              return (goal', res, modalAnd mode' mode'')


typeCheck flag mode (LetPair m (Abst xs n)) goal =
  do (t', ann, mode1) <- typeInfer flag mode m
     at <- updateWithSubst t'
     case at of
       Exists (Abst x1 b') t1 ->
         do when (length xs /= 2) $ throwError $ ArityExistsErr at xs
            let (x:y:[]) = xs
                b = n
            addVar x t1
            addVar y (apply [(x1, EigenVar x)] b')
            let b'' = apply [(x, EigenVar x)] b
            (goal', ann2, mode2) <- typeCheck flag mode b'' goal
            ann2' <- updateWithSubst ann2
            ann3 <- resolveGoals ann2'
            checkUsage y b
            checkUsage x b
            removeVar x
            removeVar y
            let res = LetPair ann (abst [x, y] ann3) 
            return (goal', res, modalAnd mode1 mode2)

       _ -> case unTensor (length xs) at of
         Just ts ->
           do let env = zip xs ts
              mapM (\ (x, t) -> addVar x t) env
              (goal', ann2, mode2) <- typeCheck flag mode n goal
              mapM (\ (x, t) -> checkUsage x n) env
              mapM removeVar xs
              ann2' <- updateWithSubst ann2
              let res = LetPair ann (abst xs ann2') 
              return (goal', res, modalAnd mode1 mode2)
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
                            (goal', ann2, mode2) <- typeCheck flag mode n (substitute sub' goal)
                            mapM (\ x -> checkUsage x n) xs
                            mapM removeVar xs
                            ann2' <- updateWithSubst ann2
                            let res = LetPair ann (abst xs ann2') 
                            return (goal', res, modalAnd mode1 mode2)

typeCheck flag mode (LetPat m bd) goal =
  do (tt, ann, mode1) <- typeInfer flag mode m
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
                 (goal'', ann2, mode2) <- typeCheck flag mode n' goal'
                 subb <- getSubst
                 mapM (\ (Right v) -> checkUsage v n >>= \ r -> (return (v, r))) vs
                 mapM_ (\ (Right v) -> removeVar v) vs
                 -- It is important to update the environment before going
                 -- out of a dependent pattern matching
                 updateLocalInst subb
                 ann2' <- resolveGoals (substitute subb ann2)
                 -- !!!! Note that let pat is ok to leak local substitution,
                 -- as the branch is really global!.
                 mapM removeLocalInst ins
                 let axs' = map (substVar subb) axs
                     goal''' = substitute subb goal''
                     res = LetPat ann (abst (PApp kid axs') ann2')
                 return (goal''', res, modalAnd mode1 mode2)
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


typeCheck flag mode a@(Case tm (B brs)) goal =
  do (t, ann, mode1) <- typeInfer flag mode tm
     at <- updateWithSubst t
     let t' = flatten at
     when (t' == Nothing) $ throwError (DataErr at tm) 
     let Just (Right id, _) = t'
     updateCountWith (\ c -> enterCase c id)
     r <- checkBrs at brs goal
     let brss = map (\ (x, y, z) -> y) r
         ms = map (\ (x, y, z) -> z) r
     updateCountWith exitCase
     let res = Case ann (B brss)
     return (goal, res, foldr modalAnd mode1 ms)
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
                         (goal'', ann2, mode') <- typeCheck flag mode m' goal'
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
                         return (goal''', abst (PApp kid axs') ann2', mode')

typeCheck flag mode tm ty = equality flag mode tm ty


-- | Infer a type for /tm/, and check if it is unifiable with /ty/.
equality :: Bool -> Modality -> Exp -> Exp -> TCMonad (Exp, Exp, Modality)
equality flag mode tm ty =
  do ty' <- updateWithSubst ty
     if not (ty == ty') then typeCheck flag mode tm ty'
       else
       do (tym, ann, mode') <- typeInfer flag mode tm
          tym1 <- updateWithSubst tym
          ty1 <- updateWithSubst ty'
          -- Here we are assuming there is no types like !!A
          case (erasePos tym1, erasePos ty1) of
            (Bang tym1' m1, Bang ty1' m2) ->
              do 
                 let s = modeResolution m1 m2
                 when (s == Nothing) $ throwError $ ModalityErr m1 m2 tm
                 let Just s' = s
                 updateModeSubst s'
                 m1' <- updateModality m1
                 mode2 <- updateModality mode'
                 (tym1'', a2, mode2') <- handleEquality tm ann tym1' ty1' mode2
                 return (Bang tym1'' (simplify m1'), a2, mode2')
            (tym1, Bang ty1 m) -> 
              throwError $ BangValue tm (Bang ty1 m)
            (Circ a1 a2 m1, Circ b1 b2 m2) ->
              do let s = modeResolution m1 m2
                 when (s == Nothing) $ throwError $ ModalityErr m1 m2 tm
                 let Just s' = s
                 updateModeSubst s'
                 m1' <- updateModality m1
                 m2' <- updateModality m2
                 mode' <- updateModality mode
                 handleEquality tm ann (Circ a1 a2 m1') (Circ b1 b2 m2') mode'
            (tym1, ty1) ->
              handleEquality tm ann tym1 ty1 mode'
  where handleEquality tm ann tym1 ty1 mode = 
          do (a2, tym', anEnv, mode') <- addAnn flag mode tm ann tym1 []
             mapM (\ (x, t) -> addVar x t) anEnv
             unifRes <- normalizeUnif tym' ty1
             case unifRes of
               Nothing -> 
                 throwError $ NotEq tm ty1 tym1
               Just s ->
                 do ss <- getSubst
                    let sub' = s `mergeSub` ss
                    updateSubst sub'
                    return (tym', a2, mode')


-- | Normalize and unify two expressions (/head/ and /t/), taking
-- dependent pattern matching into account. Dependent pattern matching
-- has the effect of converting eigenvariables into variables.
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
  where -- change relavent variables back into eigenvariables after dependent pattern-matching. 
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
-- of the pattern. It will return the following, 'Exp': head of the type expression,
-- ['Either' a 'Variable']: essentially an extended list of pattern variables,
-- ['Variable']: a list of dictionary variables, Exp: annotated version of the constructor,
-- ['Variable']: a list of eigenvariables.

extendEnv :: [Either (NoBind Exp) Variable] -> Exp -> Exp ->
             TCMonad (Exp, [Either a Variable], [Variable], Exp, [Variable])
extendEnv xs (Mod (Abst _ ty)) kid = extendEnv xs ty kid
             
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
handleTypeApp :: Exp -> Exp -> Exp -> Exp -> Modality -> TCMonad (Exp, Exp, Modality)
handleTypeApp ann t' t1 t2 m =
  case erasePos t' of
    Arrow k1 k2 ->
        do (_, ann2, _) <- typeCheck True m t2 k1
           return (k2, App' ann ann2, m)
    Pi b ty ->
      open b $ \ vs b' ->
        do (_, ann2, _) <- typeCheck True m t2 ty
           let t2' = erasePos $ toEigen ann2
           b'' <- betaNormalize (apply [(head vs, t2')]  b')
           let k2 = if null (tail vs) then b''
                      else Pi (abst (tail vs) b'') ty
           return (k2, App' ann ann2, m)
           
    a -> throwError $ KAppErr t1 (App t1 t2) a  

-- | Infer a type for a term application.
handleTermApp :: Bool -> Exp -> Exp -> Exp -> Exp -> Exp -> Modality -> Modality
                 -> TCMonad (Exp, Exp, Modality)
handleTermApp flag ann pos t' t1 t2 cMode mode1 = 
  do (a1', rt, anEnv, mode2) <- addAnn flag mode1 pos ann t' []
     mapM (\ (x, t) -> addVar x t) anEnv
     rt' <- updateWithSubst rt
     case rt' of
       Arrow ty1 ty2 | isKind ty1 ->
         do (_, ann2, _) <- typeCheck True cMode t2 ty1
            let res = AppDepTy a1' ann2
            return (ty2, res, mode2)
       Arrow ty1 ty2 ->
         do (_, ann2, cMode') <- typeCheck flag cMode t2 ty1
            let res = if flag then App' a1' ann2 else App a1' ann2
            ty2' <- updateWithModeSubst ty2
            mode2' <- updateModality mode2
            cMode'' <- updateModality cMode'
            let newMode = modalAnd mode2' cMode''
            return (ty2', res, newMode)
                    
       Arrow' ty1 ty2 ->
         do (_, ann2, _) <- typeCheck True cMode t2 ty1
            let res = App' a1' ann2
            return (ty2, res, cMode)            
       b@(Pi bind ty) ->
         open bind $
         \ xs m -> 
                -- typecheck or kind check t2
                -- since t2 may travels to m, we
                -- normalize [[t2]/x]m
             do let flag' = isKind ty
                (_, kann, cMode') <- typeCheck flag' cMode t2 ty
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
                     mode2' <- updateModality mode2
                     cMode'' <- updateModality cMode'
                     return (m'', res', modalAnd mode2' cMode'')
                  else
                  do m'' <- updateWithSubst m'
                     ty' <- updateWithSubst ty
                     res' <- updateWithSubst res
                     mode2' <- updateModality mode2
                     cMode'' <- updateModality cMode'
                     return (Pi (abst (tail xs) m'') ty', res', modalAnd mode2' cMode'')
                     
       b -> throwError $ ArrowErr t1 b


-- | Add annotations to the term /a/ according to its type if it is applied to some
-- other terms.
addAnn :: Bool -> Modality -> Exp -> Exp -> Exp -> [(Variable, Exp)] ->
          TCMonad (Exp, Exp, [(Variable, Exp)], Modality)

addAnn flag mode e a (Pos _ t) env = addAnn flag mode e a t env
addAnn flag mode e a (Mod (Abst _ t)) env = addAnn flag mode e a t env
addAnn flag mode e a (Bang t m) env =
  do let force = if flag then Force' else Force
     t' <- if flag then shape t else return t
     if flag then addAnn flag mode e (force a) t' env
       else do m' <- updateModality m
               mode' <- updateModality mode
               addAnn flag (modalAnd mode' m') e (force a) t' env

addAnn flag mode e a (Forall bd ty) env | isKind ty = open bd $ \ xs t ->
       let a' = foldl AppType a (map Var xs)
           new = map (\ x -> (x, ty)) xs
       in addAnn flag mode e a' t (new ++ env) 

addAnn flag mode e a (Forall bd ty) env | otherwise = open bd $ \ xs t ->
       let a' = foldl AppTm a (map Var xs)
           new = map (\ x -> (x, ty)) xs
       in addAnn flag  mode e a' t (new ++ env)

addAnn flag mode e a (PiImp bd ty) env | isKind ty = open bd $ \ xs t ->
       let a' = foldl AppDepTy a (map Var xs)
           new = map (\ x -> (x, ty)) xs
       in addAnn flag mode e a' t (new ++ env) 

addAnn flag mode e a (PiImp bd ty) env | otherwise = open bd $ \ xs t ->
       let app = if flag then AppDep' else AppDep
           a' = foldl app a (map Var xs)
           new = map (\ x -> (x, ty)) xs
       in addAnn flag mode e a' t (new ++ env)          

addAnn flag mode e a (Imply bds ty) env =
  do ts <- get
     let i = clock ts
         ns = zipWith (\ i b -> "#goalinst"++(show i)) [i .. ] bds
     freshNames ns $ \ ns ->
       do let instEnv = map (\ x -> (x, e)) (zip ns bds) 
              i' = i + length bds
          put ts{clock = i'}
          mapM_ (\ ((x, t), e) -> addGoalInst x t e) instEnv
          let a' = foldl AppDict a (map GoalVar ns)
          addAnn flag mode e a' ty env
    
addAnn flag mode e a t env = return (a, t, env, mode)  

