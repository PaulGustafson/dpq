module Typechecking where

import Syntax
import SyntacticOperations
import TCMonad
import TypeError
import Utils
import Normalize
import Substitution
import TypeClass

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

typeCheck True (Forall (Abst xs m) ty) a@(Set) | otherwise = 
  do p <- isParam ty
     when (not p) $ throwError (ForallLinearErr xs ty)
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
       do checkParamCxt True a
          (t, ann) <- typeCheck flag a ty
          return (Bang t, Lift ann)
       else equality flag a (Bang ty)


typeCheck False c@(Lam bind cs) t =
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
                 do insertVar x t1 
                    (t2', ann) <- typeCheck False m t2
                    uf <- checkUsage x m 
                    removeVar x
                -- x cannot appear in type annotation, so we do not
                -- need to update the ann with current substitution.
                    let res = Lam (abst [x] ann) [uf] 
                    return (Arrow t1 t2', res)
               y:ys -> 
                 do insertVar y t1 
                    (t2', ann) <- typeCheck False (Lam (abst ys m) (tail cs)) t2
                    uf <- checkUsage y m 
                    removeVar y
                    let res = Lam (abst [y] ann) [uf]
                    return (Arrow t1 t2', res)
         Pi bd ty -> 
           open bind $ \ xs m -> open bd $ \ ys b ->
                   if length xs <= length ys then
                     do let sub1 = zip ys (map EigenVar xs)
                            b' = apply sub1 b
                            (vs, rs) = splitAt (length xs) ys
                            sub2 = zip xs (map EigenVar xs)
                            m' = apply sub2 m
                        mapM_ (\ x -> insertVar x ty) xs
                        (t, ann) <- typeCheck False m'
                                    (if null rs then b' else Pi (abst rs b') ty)
                        ufs <- mapM (\ x -> checkUsage x m') xs 
                        mapM_ removeVar xs
                        -- Since xs may appear in the type annotation in ann,
                        -- we have to update ann with current substitution.
                        -- before going out of the scope of xs. We also have to
                        -- resolve the current goals because current goals may
                        -- depend on xs.
                        ann2 <- updateWithSubst ann
                        ann' <- resolveGoals ann2
                        t' <- updateWithSubst t
                        let res = LamDep (abst xs ann') ufs
                            t'' = Pi (abst xs t') ty
                        return (t'', res)
                   else
                     do let sub1 = zip ys (map EigenVar xs)
                            b' = apply sub1 b
                            (vs, rs) = splitAt (length ys) xs
                            sub2 = zip xs $ take (length ys) (map EigenVar xs)
                            m' = apply sub2 m
                        mapM_ (\ x -> insertVar x ty) vs
                        (t, ann) <- typeCheck False
                                    (if null rs then m' else Lam (abst rs m')
                                                             (map (\ r -> NonLinear) rs))
                                    b'
                        ufs <- mapM (\ x -> checkUsage x m') vs
                        mapM_ removeVar vs
                        ann1 <- updateWithSubst ann
                        t' <- updateWithSubst t
                        ann' <- resolveGoals ann1
                        let res = LamDep (abst vs ann') ufs
                        return (Pi (abst vs t') ty, res)
         b -> throwError $ LamErr c b




equality = undefined


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
