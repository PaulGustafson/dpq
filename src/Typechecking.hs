{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
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

typeInfer flag e = throwError $ Unhandle e



typeCheck flag (Pos p e) ty =
  do (ty', ann) <- typeCheck flag e ty `catchError` \ e -> throwError $ addErrPos p e
     return (ty', Pos p ann)

-- | Sort check
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

-- | Kind check
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


-- | Type check
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
     let res = if isKind ty then (Forall (abst xs $ t') ty, LamType (abst xs $ ann''))
               else (Forall (abst xs $ t') ty, LamTm (abst xs $ ann''))
     return res
    
typeCheck flag a (Imply bds ty) =
  do let ns1 = take (length bds) (repeat "#inst")
     ns <- newNames ns1
     -- Note that we update the parameter variable information here.
     updateParamInfo bds
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
          return (Bang t, Lift ann)
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
                        let res = LamDep (abst xs ann') 
                            t'' = Pi (abst xs t') ty
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
                        mapM (\ x -> checkUsage x m') vs
                        mapM_ removeVar vs
                        ann1 <- updateWithSubst ann
                        t' <- updateWithSubst t
                        ann' <- resolveGoals ann1
                        let res = LamDep (abst vs ann') 
                        return (Pi (abst vs t') ty, res)
         b -> throwError $ LamErr c b

typeCheck flag a@(Pack t1 t2) (Exists p ty) =
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
          return (Exists p ty', Pack ann1 ann2)

typeCheck flag (Let m bd) goal =
  do (t', ann) <- typeInfer flag m
     open bd $ \ x t ->
           do let vs = S.toList $ getVars NoEigen ann
                  su = zip vs (map EigenVar vs)
              m'' <- shape $ apply su ann
              addVarDef x t' m'' 
              (goal', ann2) <- typeCheck flag t goal
              checkUsage x t
              removeVar x
              ann2' <- updateWithSubst ann2
              let res = Let ann (abst x ann2') 
              return (goal', res)

typeCheck flag (LetEx m bd) goal =
  do (t', ann) <- typeInfer flag m
     at <- updateWithSubst t'
     case at of
       Exists p t1 ->
         open bd $ \ (x, y) b ->
            open p $ \ x1 b' ->
           do addVar x t1
              addVar y (apply [(x1, EigenVar x)] b')
              (goal', ann2) <- typeCheck flag b goal
              ann2' <- updateWithSubst ann2
              ann3 <- resolveGoals ann2'
              checkUsage y b
              checkUsage x b
              removeVar x
              removeVar y
              let res = LetEx ann (abst (x, y) ann3) 
              return (goal', res)
       a -> throwError $ ExistsErr m a

typeCheck flag (LetPair m (Abst xs n)) goal =
  do (t', ann) <- typeInfer flag m
     at <- updateWithSubst t'
     case unTensor (length xs) at of
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
         do ns <- newNames $ map (\ x -> "#unif") xs
            freshNames ns $ \ (h:ns) ->
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
          (head, axs, ins, kid') <- extendEnv isSemi vs dt (Const kid)
          let matchEigen = isEigenVar m
              isDpm = isSemi || matchEigen
          when (isSemi && matchEigen) $
            error "matchEigen and matchEigen cannot be true at the same time."
          when isDpm $ checkRetro m ss
          unifRes <- patternUnif m isDpm index head t'
          case unifRes of
            Nothing ->
              throwError $ withPosition m (UnifErr head t') 
            Just sub' -> do
                 sub1 <- if matchEigen 
                         then makeSub m sub' $
                              foldl (\ x (Right y) -> App x (EigenVar y)) kid' vs
                         else return sub'
                 let sub'' = sub1 `mergeSub` ss
                 updateSubst sub''
                 let goal' = substitute sub'' goal
                 (goal'', ann2) <- typeCheck flag n goal'
                 subb <- getSubst
                 mapM (\ (Right v) -> checkUsage v n >>= \ r -> (return (v, r))) vs
                 mapM_ (\ (Right v) -> removeVar v) vs
                 -- It is important to update the environment before going
                 -- out of a dependent pattern matching
                 updateLocalInst subb
                 ann2' <- resolveGoals (substitute subb ann2)
                 -- !!!! Note that let pat is ok to leak local substitution,
                 -- as the branch is really global!. 
                 mapM removeInst ins
                 let axs' = if isDpm then map (substVar subb) axs else axs
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
                  (head, axs, ins, kid') <- extendEnv isSemi vs dt (Const kid)
                  let matchEigen = isEigenVar tm
                      isDpm = isSemi || matchEigen
                  ss <- getSubst
                  when (isSemi && matchEigen) $
                    error "matchEigen and matchEigen cannot be true at the same time."
                  when isDpm $ checkRetro tm ss
                  unifRes <- patternUnif tm isDpm index head t
                  case unifRes of
                    Nothing -> throwError $ withPosition tm (UnifErr head t) 
                    Just sub' -> do
                         sub1 <- if matchEigen then
                                      makeSub tm sub' $
                                      foldl (\ x (Right y) -> App x (EigenVar y)) kid' vs
                                 else return sub'
                         let sub'' = sub1 `mergeSub` ss
                         updateSubst sub''
                         -- We use special substitution for goal
                         let goal' = substitute sub'' goal 
                         (goal'', ann2) <- typeCheck flag m goal'
                         subb <- getSubst 
                         mapM (\ (Right v) -> checkUsage v m >>=
                                                          \ r -> return (v, r)) vs

                         updateLocalInst subb
                         
                         -- we need to restore the substitution to ss
                         -- because subb' may be influenced by dependent pattern matching.
                         let goal''' = substitute subb goal''
                         ann2' <- resolveGoals (substitute subb ann2)
                                  
                         when isDpm $ updateSubst ss
                         when (not isDpm) $ updateSubst subb
                         
                         -- because the variable axs may be in the domain
                         -- of the substitution, hence it is necessary to update
                         -- axs as well before binding.
                         let axs' = if isSemi || matchEigen then map (substVar subb) axs else axs
                         mapM_ (\ (Right v) -> removeVar v) vs
                         mapM removeInst ins
                         return (goal''', abst (PApp kid axs') ann2')

typeCheck flag tm ty = equality flag tm ty

equality flag tm ty =
  do ty' <- updateWithSubst ty
     if not (ty == ty') then typeCheck flag tm ty'
       else
       do (tym, ann) <- typeInfer flag tm
          tym1 <- updateWithSubst tym
          ty1 <- updateWithSubst ty'
          -- Here we are assuming there is no types like !!A
          case (tym1, ty1) of
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
                 do tyN1 <- normalize tym'
                    tyN2 <- normalize ty1
                    throwError $ NotEq tm tyN2 tyN1
               Just s ->
                 do ss <- getSubst
                    let sub' = s `mergeSub` ss
                    updateSubst sub'
                    return (ty1, a2)



-- | normalized and unify two expression
patternUnif m isDpm index head t =
  if isDpm then
    case index of
        Nothing -> normalizeUnif head t
        Just i ->
          case flatten t of
            Just (Right h, args) -> 
              let (bs, a:as) = splitAt i args
                  a' = unEigen a
                  t' = foldl App' (LBase h) (bs++(a':as))
              in normalizeUnif head t'
            _ -> throwError $ withPosition m (UnifErr head t)
  else normalizeUnif head t
--    (False, True) -> normalizeUnif head t
      

normalizeUnif t1 t2 =
 do t1' <- resolveGoals t1
    t2' <- resolveGoals t2
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


extendEnv isSemi xs (Forall bind ty) kid | isKind ty =
  open bind $
      \ ys t' ->
      do mapM_ (\ x -> addVar x ty) ys
         let kid' = foldl AppType kid (map Var ys)
         extendEnv isSemi xs t' kid'

extendEnv isSemi xs (Forall bind ty) kid | otherwise =
  open bind $
      \ ys t' ->
      do mapM_ (\ x -> addVar x ty) ys
         let kid' = foldl AppTm kid (map Var ys)
         (h, vs, ins, kid'') <- extendEnv isSemi xs t' kid'
         let vs' = if isSemi then (map Right ys)++vs else vs
         return (h, vs', ins, kid'')

extendEnv isSemi xs (Imply bds ty) kid =
  do let ns1 = take (length bds) (repeat "#inst")
     ns <- newNames ns1
     freshNames ns $ \ ns ->
       do mapM_ (\ (x, y) -> insertLocalInst x y) (zip ns bds)
          let kid' = foldl AppDict kid (map Var ns)
          (h, vs, ins, kid'') <- extendEnv isSemi xs ty kid'
          return (h, (map Right ns)++vs, ns++ins, kid'')

extendEnv isSemi [] t kid = return (t, [], [], kid)

extendEnv isSemi (Right x:xs) (Arrow t1 t2) kid =
  do addVar x t1
     (h, ys, ins, kid') <- extendEnv isSemi xs t2 kid
     return (h,  Right x : ys, ins, kid')

extendEnv isSemi (Right x : xs) (Pi bind ty) kid
  | not (isKind ty) =
    open bind $ \ ys t' ->
    do let y = head ys
           t'' = apply [(y , EigenVar x)] t'  -- note that Pi is existential
       addVar x ty
       if null (tail ys)
         then do (h, ys, ins, kid') <- extendEnv isSemi xs t'' kid
                 return (h, (Right x : ys), ins, kid')
         else do (h, ys, ins, kid') <- extendEnv isSemi xs (Pi (abst (tail ys) t'') ty) kid
                 return (h, (Right x : ys), ins, kid')

     
extendEnv isSemi a b kid = throwError $ ExtendEnvErr a b



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

