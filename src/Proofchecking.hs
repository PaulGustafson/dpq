{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}


module Proofchecking where


import Syntax
import SyntacticOperations
import TCMonad
import Normalize
import TypeError
import Unification
import Substitution
import Utils

import Nominal
import Control.Monad.Except
import qualified Data.Set as S
import qualified Data.Map as Map
import Data.Map (Map)
import Debug.Trace


-- | A bidirectional proof checker that is mutually defined with proofInfer.
-- The flag indicates if it is a pure type checking
proofCheck :: Bool -> Exp -> Exp -> TCMonad ()
proofInfer :: Bool -> Exp -> TCMonad Exp



proofInfer flag (LBase kid) =
  lookupId kid >>= \ x -> return $ (classifier x)
proofInfer flag (Base kid) =
  lookupId kid >>= \ x -> return $ (classifier x)
proofInfer flag Unit = return Set
proofInfer flag Set = return Sort
-- proofInfer flag (Bang ty) =
--   do a <- proofInfer True ty
--      case a of
--        Set -> return Set
--        b -> throwPfError (NotEq ty Set b)



proofInfer flag ty@(Arrow t1 t2) =
  do a1 <- proofInfer True t1
     a2 <- proofInfer True t2
     case (a1, a2) of
       (Set, Set) -> return Set
       (Set, Sort) -> return Sort
       (Sort, Sort) -> return Sort
       (b1, b2) -> throwError (NotEq ty Set (Arrow b1 b2))


proofInfer flag ty@(Circ t1 t2) =
  do a1 <- proofInfer True t1
     a2 <- proofInfer True t2
     case (a1, a2) of
       (Set, Set) -> return Set
       (b1, b2) -> throwError (NotEq ty Set (Circ b1 b2))

proofInfer flag a@(Imply [] t) =
  do ty <- proofInfer True t
     case ty of
       Set -> return Set
       _ -> throwError (NotEq t Set ty)
       
proofInfer flag a@(Imply (x:xs) t) =
  do ty <- proofInfer True x
     updateParamInfo [x]
     case ty of
       Set -> proofInfer True (Imply xs t)
       _ -> throwError (NotEq x Set ty)

proofInfer flag (Bang ty) =
  do a <- proofInfer True ty
     case a of
       Set -> return Set
       b -> throwError (NotEq ty Set b)

proofInfer flag ty@(Tensor t1 t2) =
  do a1 <- proofInfer True t1
     a2 <- proofInfer True t2
     case (a1, a2) of
       (Set, Set) -> return Set
       (b1, b2) -> throwError (NotEq ty Set (Tensor b1 b2))

proofInfer flag ty@(Exists bd t) =
  do a <- proofInfer True t
     case a of
       Set ->
         open bd $ \ x m ->
         do addVar x t
            tm <- proofInfer True m
            removeVar x
            case tm of
              Set -> return Set
              _ -> throwError (NotEq m Set tm)
       _ -> throwError (NotEq t Set a)
       
proofInfer flag ty@(Pi bd t) =
  do a <- proofInfer True t
     case a of
       Set ->
         open bd $ \ xs m ->
         do mapM_ (\ x -> addVar x t) xs
            tm <- proofInfer True m
            mapM_ removeVar xs
            case tm of
              Set -> return Set
              _ -> throwError (NotEq m Set tm)
       Sort ->
         open bd $ \ xs m ->
         do mapM_ (\ x -> addVar x t) xs
            tm <- proofInfer True m
            mapM_ removeVar xs
            case tm of
              Set -> return Set
              _ -> throwError (NotEq m Set tm)
       _ -> throwError (NotEq t Set a)

proofInfer flag ty@(Forall bd t) =
  do a <- proofInfer True t
     case a of
       Set ->
         open bd $ \ xs m ->
         do mapM_ (\ x -> addVar x t) xs
            tm <- proofInfer True m
            mapM_ removeVar xs
            case tm of
              Set -> return Set
              _ -> throwError (NotEq m Set tm)
       _ -> throwError (NotEq t Set a)

proofInfer flag a@(Var x) =
  do (t, _) <- lookupVar x
     if flag then shape t 
       else
       do updateCount x
          return t

proofInfer flag a@(EigenVar x) =
  do (t, _) <- lookupVar x
     if flag then shape t 
       else
       do updateCount x
          return t
  

proofInfer flag a@(Const kid) =
  do funPac <- lookupId kid
     let cl = classifier funPac
     if flag then shape cl else return cl


proofInfer False a@(AppDep t1 t2) =
  do t' <- proofInfer False t1
     case t' of
       b@(Pi bd ty) -> open bd $ \ xs m ->
         do let isK = isKind ty
            proofCheck isK t2 ty
            let vs = S.toList $ getVars NoEigen t2
                su = zip vs (map EigenVar vs)
                t2' = apply su t2
            t2'' <- if isK then return t2' else shape t2'
            m' <- betaNormalize (apply [(head xs, t2'')] m) 
            if null (tail xs)
              then return m'
              else return $ Pi (abst (tail xs) m') ty
       b@(PiImp bd ty) -> open bd $ \ xs m ->
         do let isK = isKind ty
            proofCheck isK t2 ty
            let vs = S.toList $ getVars NoEigen t2
                su = zip vs (map EigenVar vs)
                t2' = apply su t2
            t2'' <- if isK then return t2' else shape t2'
            m' <- betaNormalize (apply [(head xs, t2'')] m) 
            if null (tail xs)
              then return m'
              else return $ PiImp (abst (tail xs) m') ty  
                   
       b -> throwError $ ArrowErr t1 b

proofInfer True a@(AppDep' t1 t2) =
  do t' <- proofInfer True t1
     case t' of
       b@(Pi' bd ty) -> open bd $ \ xs m ->
         do proofCheck True t2 ty
            let vs = S.toList $ getVars NoEigen t2
                su = zip vs (map EigenVar vs)
                t2' = apply su t2
            m' <- betaNormalize (apply [(head xs, t2')] m) 
            if null (tail xs)
              then return m'
              else return $ Pi' (abst (tail xs) m') ty  
       b -> throwError $ ArrowErr t1 b

proofInfer flag a@(App t1 t2) =
  do t' <- proofInfer flag t1
     case t' of
       Arrow ty m -> proofCheck flag t2 ty >> return m
       b -> throwError $ ArrowErr t1 b


proofInfer flag a@(App' t1 t2) =
  do t' <- proofInfer True t1
     case t' of
       Arrow ty m | isKind t' -> proofCheck True t2 ty >> return m
       Arrow' ty m -> proofCheck True t2 ty >> return m
       b@(Pi bd ty) | isKind b -> open bd $ \ xs m ->
         do
            proofCheck True t2 ty
            let vs = S.toList $ getVars NoEigen t2
                su = zip vs (map EigenVar vs)
                t2' = apply su t2
            m' <- betaNormalize (apply [(head xs, t2')]  m) 
            if null (tail xs)
              then return m'
              else return $ Pi (abst (tail xs) m') ty  
       b -> throwError $ ArrowErr t1 b

proofInfer flag a@(AppDict t1 t2) =
  do t' <- proofInfer flag t1
     case t' of
       Imply (ty:[]) m -> proofCheck True t2 ty >> return m
       Imply (ty:res) m -> proofCheck True t2 ty >> return (Imply res m)
       b -> throwError $ ArrowErr t1 b

proofInfer flag a@(AppType t1 t2) =
  proofInfer flag t1 >>= \ t' -> handleForallApp flag t' t1 t2

proofInfer flag a@(AppTm t1 t2) =
  proofInfer flag t1 >>= \ t' -> handleForallApp flag t' t1 t2

proofInfer flag Revert =
  freshNames ["a", "b"] $ \ [a, b] ->
  let va = Var a
      vb = Var b
      t1 = Arrow (Circ va vb) (Circ vb va)
      ty = Forall (abst [a, b] t1) Set
  in return ty

proofInfer flag UnBox =
  freshNames ["a", "b"] $ \ [a, b] ->
  let va = Var a
      vb = Var b
      t1 = Arrow (Circ va vb) (Bang (Arrow va vb))
      ty = Forall (abst [a, b] t1) Set
  in return ty

proofInfer flag t@(Box) = freshNames ["a", "b"] $ \ [a, b] ->
  do let va = Var a
         vb = Var b
         simpClass = Id "Simple"
         t1 = Arrow (Bang (Arrow va vb)) (Circ va vb)
         t1' = Imply [(App' (Base simpClass) va), (App' (Base simpClass) vb)] t1
         boxType = Pi (abst [a] (Forall (abst [b] t1') Set)) Set
     return boxType

proofInfer flag t@(RunCirc) = freshNames ["a", "b", "c", "d"] $ \ [a, b, c, d] ->
  do let va = Var a
         vb = Var b
         vc = Var c
         vd = Var d
         simpParam = Id "SimpParam"
         t1 = Arrow (Circ va vb) (Arrow vc vd)
         t1' = Imply [App' (App' (Base simpParam) va) vc , App' (App' (Base simpParam) vb) vd] t1
         res = Forall (abst [a, b, c, d] t1') Set
     return res

proofInfer flag t@(ExBox) =
  freshNames ["a", "b", "p", "n"] $ \ [a, b, p, n] ->
  do let va = Var a
         vb = Var b
         vp = Var p
         vn = Var n
         kp = Arrow vb Set
         simpClass = Id "Simple"
         paramClass = Id "Parameter"
         simpA = App' (Base simpClass) va
         paramB = App' (Base paramClass) vb
         simpP = App' (Base simpClass) (App' vp vn)
         t1Output = Exists (abst n (App' vp vn)) (vb)
         t1 = Bang (Arrow va t1Output)
         output = Exists (abst n $ Imply [simpP] (Circ va (App' vp vn))) (vb)
         beforePi = Arrow t1 output
         r = Pi (abst [a] $
                 Forall (abst [b] (Imply [paramB] $ Pi (abst [p] $ Imply [simpA] beforePi) kp)) Set) Set
     return r

proofInfer flag (Star) = return Unit
       
proofInfer False a@(Force t) =
  do ty <- proofInfer False t
     case ty of
       Bang ty' -> return ty'
       b -> throwError $ BangErr t b 

proofInfer True a@(Force' t) =
  do ty <- proofInfer True t
     case ty of
       Bang ty' -> shape ty'
       b -> throwError $ BangErr t b 

proofInfer flag a@(Pair t1 t2) =
  do ty1 <- proofInfer flag t1 
     ty2 <- proofInfer flag t2
     return $ (Tensor ty1 ty2)

proofInfer flag (Pos p e) = 
  proofInfer flag e `catchError` \ e -> throwError $ collapsePos p e

proofInfer flag (WithType a t) =
  do proofCheck True t Set
     let t' = toEigen t
     proofCheck False a t'
     return t'

proofInfer flag e = throwError $ Unhandle e

proofCheck flag (Pos p e) t = 
  proofCheck flag e t `catchError` \ e -> throwError $ collapsePos p e

proofCheck False a@(Lam bd) (Arrow t1 t2) = open bd $ \ xs m ->
  do addVar (head xs) t1
     proofCheck False (if (null $ tail xs) then m else (Lam (abst (tail xs) m))) t2
     checkUsage (head xs) m

proofCheck True a@(Lam' bd) (Arrow' t1 t2) = open bd $ \ xs m ->
  do addVar (head xs) t1
     proofCheck True (if (null $ tail xs) then m else (Lam' (abst (tail xs) m))) t2

proofCheck flag a@(Lam' bd) b@(Arrow t1 t2) | isKind b = open bd $ \ xs m ->
  do addVar (head xs) t1
     proofCheck True (if (null $ tail xs) then m else (Lam' (abst (tail xs) m))) t2

proofCheck flag a@(LamDict bd) (Imply (t1:[]) t2) = open bd $ \ xs m ->
  do addVar (head xs) t1
     updateParamInfo [t1]
     proofCheck flag (if (null $ tail xs) then m else (LamDict (abst (tail xs) m))) t2

proofCheck flag a@(LamDict bd) (Imply (t1:ts) t2) = open bd $ \ xs m ->
  do addVar (head xs) t1
     updateParamInfo [t1]
     proofCheck flag (if (null $ tail xs) then m else (LamDict (abst (tail xs) m))) (Imply ts t2)


proofCheck False a@(LamDep bd1) exp@(Pi bd2 ty) =
  handleAbs False LamDep Pi bd1 bd2 ty True

proofCheck False a@(LamDep bd1) exp@(PiImp bd2 ty) =
  handleAbs False LamDep PiImp bd1 bd2 ty False

proofCheck True a@(LamDep' bd1) exp@(Pi' bd2 ty) =
  handleAbs True LamDep' Pi' bd1 bd2 ty False

proofCheck flag (LamTm bd1) exp@(Forall bd2 ty) =
  handleAbs flag LamTm Forall bd1 bd2 ty False

proofCheck flag (LamType bd1) exp@(Forall bd2 ty) =
  handleAbs flag LamType Forall bd1 bd2 ty False

proofCheck flag (Lift m) (Bang t) =
  do checkParamCxt m
     proofCheck flag m t

proofCheck flag a@(Pack t1 t2) (Exists p ty)=
  do proofCheck flag t1 ty
     open p $ \ x t ->
       do let vars = S.toList $ getVars NoEigen t1
              sub1 = zip vars (map EigenVar vars)
              t1Eigen = apply sub1 t1
          ts <- shape t1Eigen
          let t' = apply [(x, ts)] t
          proofCheck flag t2 t'

proofCheck flag (Let m bd) goal = open bd $ \ x t ->
  do t' <- proofInfer flag m
     let vs = S.toList $ getVars NoEigen m
         su = zip vs (map EigenVar vs)
     m'' <- shape $ apply su m
     addVarDef x t' m''
     r <- proofCheck flag t goal
     when (not flag) $ checkUsage x t
     removeVar x
     return r

proofCheck flag (LetPair m bd) goal = open bd $ \ xs t ->
  do t' <- proofInfer flag m
     case unTensor (length xs) t' of
       Just ts ->
         do let env = zip xs ts
            mapM (\ (x, y) -> addVar x y) env
            res <- proofCheck flag t goal
            when (not flag) $ mapM_ (\x -> checkUsage x t) xs
            mapM removeVar xs
            return res
       Nothing -> throwError $ TensorErr (length xs) m t'

proofCheck flag (LetEx m bd) goal = open bd $ \ (x, y) t ->
  do t' <- proofInfer flag m
     case t' of
       Exists p t1 ->
         open p $ \ z t2 ->
         do addVar x t1
            let t2' = apply [(z, EigenVar x)] t2
            addVar y t2'
            proofCheck flag t goal
            when (not flag) $ checkUsage x t >> checkUsage y t 
            removeVar x
            removeVar y
       b -> throwError $ ExistsErr m b


proofCheck flag (LetPat m bd) goal  = open bd $ \ (PApp kid args) n ->
  do tt <- proofInfer flag m
     funPac <- lookupId kid
     let dt = classifier funPac
     (isSemi, index) <- isSemiSimple kid
     (head, vs, kid') <- inst dt args (Const kid)
     -- tt' <- normalize tt
     let matchEigen = isEigenVar m
         isDpm = isSemi || matchEigen
     unifRes <- dependentUnif index isDpm head tt
     ss <- getSubst
     case unifRes of
       Nothing -> throwError $ (UnifErr head tt)
       Just sub' -> do
            sub1 <- if matchEigen then
                      makeSub m sub' $ foldl (\ x y ->
                                           case y of
                                             Right u -> App x (EigenVar u)
                                             Left (NoBind u) -> App x u
                                         ) kid' vs
                         
                    else return sub'
            let sub'' = sub1 `mergeSub` ss
            updateSubst sub''
            let goal' = substitute sub'' goal
            proofCheck flag n goal'
            mapM_ (\ v ->
                    case v of
                      Right x ->
                        do when (not flag) $ checkUsage x n 
                           removeVar x
                      _ -> return ()
                  ) vs
       where makeSub (EigenVar x) s u =
               do u' <- shape $ substitute s u
                  return $ s `Map.union` Map.fromList [(x, u')]
             makeSub (Pos p x) s u = makeSub x s u
             makeSub a s u = return s


proofCheck flag a@(Case tm (B brs)) goal =
  do t <- proofInfer flag tm
     let t' = flatten t 
     when (t' == Nothing) $ throwError (DataErr t tm)
     let Just (Left id, _) = t'
     updateCountWith (\ x -> enterCase x id)
     checkBrs t brs goal
     updateCountWith exitCase
  where 
        makeSub (EigenVar x) s u =
          do u' <- shape $ substitute s u
             return $ s `Map.union` Map.fromList [(x, u')]
        makeSub (Pos p x) s u = makeSub x s u
        makeSub a s u = return s

        checkBrs t pbs goal = 
          mapM (checkBr t goal) pbs

        checkBr t goal pb = open pb $ \ (PApp kid args) m ->
          do funPac <- lookupId kid
             let dt = classifier funPac
             updateCountWith (\ x -> nextCase x kid)
             (isSemi, index) <- isSemiSimple kid
             (head, vs, kid') <- inst dt args (Const kid)
             let matchEigen = isEigenVar tm
                 isDpm = isSemi || matchEigen
             ss <- getSubst
             unifRes <- dependentUnif index isDpm head t
             case unifRes of
               Nothing -> throwError $ (UnifErr head t)
               Just sub' -> do
                 sub1 <-
                   if matchEigen then
                     makeSub tm sub' $ foldl (\ x y ->
                                               case y of
                                                 Right u -> App x (EigenVar u)
                                                 Left (NoBind u) -> App x u
                                             ) kid' vs
                     
                   else return sub'
                 let sub'' = sub1 `mergeSub` ss
                 updateSubst sub''
                 let goal' = substitute sub'' goal
                 proofCheck flag m goal'
                 mapM_ (\ v ->
                         case v of
                           Right x ->
                             do when (not flag) $ checkUsage x m 
                                removeVar x
                           _ -> return ()
                       ) vs
                 updateSubst ss

proofCheck flag a goal =
  do t <- proofInfer flag a
     t1 <- updateWithSubst t
     goal1 <- updateWithSubst goal
     goal' <- normalize goal1
     t' <- normalize t1
     when ((erasePos goal') /= (erasePos t')) $ throwError (NotEq a goal' t')


dependentUnif index isDpm head t =
  if not isDpm then return $ runUnify head t
  else case index of
         Nothing -> return $ runUnify head t
         Just i ->
           case flatten t of
            Just (Right h, args) -> 
              let (bs, a:as) = splitAt i args
                  vars = S.toList $ getVars OnlyEigen a
                  eSub = zip vars (map EigenVar vars)
                  a' = unEigenBound vars a
                  t' = foldl App' (LBase h) (bs++(a':as))
              in case runUnify head t' of
                   Nothing -> return Nothing
                   Just subst -> 
                     helper subst vars eSub
            _ -> throwError $ UnifErr head t
  where -- change relavent variables back into eigenvariables after dependent pattern-matching 
        helper subst (v:vars) eSub =
          let subst' = Map.mapWithKey (\ k val -> if k == v then toEigen val else val) subst
              subst'' = Map.map (\ val -> apply eSub val) subst'
          in helper subst'' vars eSub
        helper subst [] eSub = return $ Just subst


handleForallApp flag t' t1 t2 = 
     case erasePos t' of
       b@(Forall bd kd) -> helper bd kd
       b -> throwError $ ArrowErr t1 b
     where helper bd kd =
             open bd $ \ xs m ->
              do let vs = S.toList $ getVars NoEigen t2
                     su = zip vs (map EigenVar vs)
                     t2' = apply su t2
                 proofCheck True t2 kd
                 m' <- betaNormalize (apply [(head xs,  t2')] m)
                 m'' <- if flag then shape m' else return m'
                 if null (tail xs)
                   then return m''
                   else return $ Forall (abst (tail xs) m'') kd

-- throwError e = throwError $ ProofCheckErr e

handleAbs flag lam prefix bd1 bd2 ty fl =
  open bd1 $ \ xs m -> open bd2 $ \ ys b ->
  if length xs <= length ys
  then do let sub = zip ys (map EigenVar xs)
              b' = apply sub b
              sub2 = zip xs (map EigenVar xs)
              (vs, rs) = splitAt (length xs) ys
              m' = apply sub2 m
          mapM_ (\ x -> addVar x ty) xs
          proofCheck flag m' (if null rs then b'
                              else prefix (abst rs b') ty)
          when fl $ mapM_ (\ x -> checkUsage x m') xs   
          mapM_ removeVar xs
  else 
    do let sub = zip ys (map EigenVar xs)
           b' = apply sub b
           (vs, rs) = splitAt (length ys) xs
           sub2 = zip xs $ take (length ys) (map EigenVar xs)
           m' = apply sub2 m
       mapM_ (\ x -> addVar x ty) vs
       proofCheck flag (if null rs then m' else lam (abst rs m')) b'
       when fl $ mapM_ (\ x -> checkUsage x m') vs
       mapM_ removeVar vs


inst (Arrow t1 t2) (Right x : xs) kid =
  do addVar x t1
     (h, vs, kid') <- inst t2 xs kid
     return (h, Right x : vs, kid')

inst (Imply [t1] t2) (Right x : xs) kid =
  do addVar x t1
     (h, vs, kid') <- inst t2 xs kid
     return (h, Right x : vs, kid')

inst (Imply (t1:ts) t2) (Right x : xs) kid =
  do addVar x t1
     (h, vs, kid') <- inst (Imply ts t2) xs kid
     return (h, Right x : vs, kid')

inst (Pi bd t) (Right x:xs) kid | not (isKind t) = open bd $ \ ys t' ->
  do let y = head ys
         t'' = apply [(y, EigenVar x)] t' 
     if null (tail ys)
       then do addVar x t
               (h, xs', kid') <- inst t'' xs kid 
               return (h, Right x:xs', kid')
       else do addVar x t
               (h, xs', kid') <- inst (Pi (abst (tail ys) t'') t) xs kid
               return (h, Right x:xs', kid')

-- inst isSemi (Forall bd ty) xs kid | isKind ty = open bd $ \ ys t' -> 
--   do mapM_ (\ x -> addVar x ty) ys
--      let kid' = foldl AppType kid (map Var ys)
--      (h, xs', kid'') <- inst isSemi t' xs kid'
--      return (h, xs', kid'')

-- not in dependent pattern matching mode
-- inst False (Forall bd ty) xs kid = open bd $ \ ys t' -> 
--   do mapM_ (\ x -> addVar x ty) ys
--      let kid' = foldl AppTm kid (map Var ys)
--      (h, xs', kid'') <- inst False t' xs kid'
--      return (h, xs', kid'')


inst (Forall bd t) (Right x:xs) kid = open bd $ \ ys t' ->
  do let y = head ys
         t'' = apply [(y, EigenVar x)] t'
     if null (tail ys)
       then do addVar x t
               (h, xs', kid') <- inst t'' xs kid
               return (h, Right x:xs', kid')
       else do addVar x t
               (h, xs', kid') <- inst (Forall (abst (tail ys) t'') t) xs kid
               return (h, Right x:xs', kid')

inst (Forall bd t) (Left (NoBind x):xs) kid = open bd $ \ ys t' ->
  do let y = head ys
         fvs = S.toList $ getVars NoEigen x
         fvs' = map EigenVar fvs
         sub = zip fvs fvs'
         x' = apply sub x
         t'' = apply [(y, x')] t' 
     if null (tail ys)
       then do (h, xs', kid') <- inst t'' xs kid
               return (h, Left (NoBind x'):xs', kid')
       else do (h, xs', kid') <- inst (Forall (abst (tail ys) t'') t) xs kid
               return (h, Left (NoBind x'):xs', kid')

inst t [] kid = return (t, [], kid)            
-- inst flag a b kid = throwError $ InstEnvErr a b
