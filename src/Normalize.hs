{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
module Normalize where

import Syntax
import SyntacticOperations
import TypeError
import TCMonad
import Utils
import Substitution

import Nominal


import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad.Except
import Control.Monad.State
import Debug.Trace

betaNormalize :: Exp -> TCMonad Exp
betaNormalize a@(Var x) = return a
betaNormalize a@(EigenVar x) = return a
betaNormalize a@(GoalVar x) = return a
betaNormalize a@(Unit) = return a
betaNormalize a@(Set) = return a
betaNormalize a@(Sort) = return a
betaNormalize a@(LBase _) = return a          
betaNormalize a@(Base _) = return a
betaNormalize a@(Lam' bd) = return a
betaNormalize a@(Lam bd) = return a
betaNormalize a@(LamDep' bd) = return a
betaNormalize a@(LamDep bd) = return a
betaNormalize a@(LamType bd) = return a
betaNormalize a@(LamTm bd) = return a
betaNormalize a@(Box) = return a
betaNormalize a@(ExBox) = return a
betaNormalize a@(UnBox) = return a
betaNormalize a@(Revert) = return a
betaNormalize a@(RunCirc) = return a
betaNormalize a@(Wired y) = return a

betaNormalize a@(Lift x) = 
  do x' <- betaNormalize x
     return $ Lift x'

betaNormalize (Force x) =
  do x' <- betaNormalize x
     case x' of
       Lift m -> betaNormalize m
       a -> return $ Force a

betaNormalize (Force' x) =
  do x' <- betaNormalize x
     case x' of
       Lift m ->
         shape m >>= betaNormalize 
       a -> return $ Force' a

betaNormalize a@(Tensor t1 t2) = 
  do t1' <- betaNormalize t1
     t2' <- betaNormalize t2
     return $ Tensor t1' t2'

betaNormalize a@(Bang t) = 
  do t' <- betaNormalize t
     return $ Bang t'

betaNormalize a@(Arrow t1 t2) =
  do t1' <- betaNormalize t1
     t2' <- betaNormalize t2
     return $ Arrow t1' t2'

betaNormalize a@(Arrow' t1 t2) =
  do t1' <- betaNormalize t1
     t2' <- betaNormalize t2
     return $ Arrow' t1' t2'

betaNormalize a@(Imply t1 t2) =
  do t1' <- mapM betaNormalize t1
     t2' <- betaNormalize t2
     return $ Imply t1' t2'


betaNormalize a@(Circ t1 t2) = 
  do t1' <- betaNormalize t1
     t2' <- betaNormalize t2
     return $ Circ t1' t2'

betaNormalize a@(Pi bd t) =
  open bd $ \ xs t' ->
    do t1 <- betaNormalize t
       t2 <- betaNormalize t'
       return $ Pi (abst xs t2) t1 

betaNormalize a@(Exists bd t) =
  open bd $ \ xs t' ->
    do t1 <- betaNormalize t
       t2 <- betaNormalize t'
       return $ Exists (abst xs t2) t1 

betaNormalize a@(Forall bd ty) =
  open bd $ \ xs t' ->
    do  t2 <- betaNormalize t'
        ty' <- betaNormalize ty
        return $ Forall (abst xs t2) ty'

betaNormalize a@(Star) = return a

betaNormalize a@(Const kid) = return a

betaNormalize a@(Pair m1 m2) = 
  do m1' <- betaNormalize m1
     m2' <- betaNormalize m2
     return $ Pair m1' m2'

betaNormalize a@(Pack m1 m2) = 
  do m1' <- betaNormalize m1
     m2' <- betaNormalize m2
     return $ Pack m1' m2'

betaNormalize (Let m bd) =
  do m' <- betaNormalize m
     return (Let m' bd)

betaNormalize (LetEx m bd) =
  do m' <- betaNormalize m
     return (LetEx m' bd)

betaNormalize a@(LetPair m bd) =
  do m' <- betaNormalize m
     return (LetPair m' bd)

betaNormalize  a@(LetPat m bd) =
  do m' <- betaNormalize m
     return $ LetPat m' bd

betaNormalize (AppType t1 t2) =
  do t1' <- betaNormalize t1
     t2' <- betaNormalize t2
     case t1' of
       LamType bd -> 
         open bd $ \ xs m ->
         let x = head xs in
         case tail xs of
           [] -> betaNormalize $ apply [(x, t2')] m
           t -> return $ LamType $ abst t (apply [(x, t2')] m)
       b -> return (AppType b t2')
            

betaNormalize (AppTm t1 t2) =
  do t1' <- betaNormalize t1
     t2' <- betaNormalize t2
     case t1' of
       LamTm bd -> 
         open bd $ \ xs m ->
         let x = head xs in
         case tail xs of
           [] -> betaNormalize $ apply [(x, t2')] m
           t -> return $ LamTm $ abst t (apply [(x, t2')] m)
       b -> return (AppTm b t2')
            
betaNormalize (AppDep t1 t2) =
  do t1' <- betaNormalize t1
     t2' <- betaNormalize t2
     case t1' of
       LamDep bd -> 
         open bd $ \ xs m ->
         let x = head xs in
         case tail xs of
           [] -> betaNormalize $ apply [(x, t2')] m
           t -> return $ LamDep (abst t (apply [(x, t2')] m))
       b -> return (AppDep b t2')

betaNormalize (AppDep' t1 t2) =
  do t1' <- betaNormalize t1
     t2' <- betaNormalize t2
     case t1' of
       LamDep' bd -> 
         open bd $ \ xs m ->
         let x = head xs in
         case tail xs of
           [] -> betaNormalize $ apply [(x, t2')] m
           t -> return $ LamDep' (abst t (apply [(x, t2')] m))
       b -> return (AppDep' b t2')

betaNormalize (AppDict t1 t2) =
  do t1' <- betaNormalize t1
     t2' <- betaNormalize t2
     case t1' of
       LamDict bd -> 
         open bd $ \ xs m ->
         let x = head xs in
         case tail xs of
           [] -> betaNormalize $ apply [(x, t2')] m
           t -> return $ LamDict (abst t (apply [(x, t2')] m))
       b -> return (AppDict b t2')       


betaNormalize (App' t1 t2) =
  do t1' <- betaNormalize t1
     t2' <- betaNormalize t2
     case t1' of
       Lam' bd -> 
         open bd $ \ xs m ->
         let x = head xs in
         case tail xs of
           [] -> betaNormalize $ apply [(x, t2')] m
           t -> return $ Lam' (abst t (apply [(x, t2')] m))
       b -> return (App' b t2')

betaNormalize (App t1 t2) =
  do t1' <- betaNormalize t1
     t2' <- betaNormalize t2
     case t1' of
       Lam bd -> 
         open bd $ \ xs m ->
         let x = head xs in
         case tail xs of
           [] -> betaNormalize $ apply [(x, t2')] m
           t -> return $ Lam (abst t (apply [(x, t2')] m))
       b -> return (App b t2')

betaNormalize a@(Case t (B brs)) =
  do t' <- betaNormalize t
     return $ Case t' (B brs)

betaNormalize (Pos _ e) = betaNormalize e
betaNormalize a = error $ "from betaNormalize" ++ (show (disp a))

normalize a@(Var x) =
  do ts <- get
     let lc = localCxt $ lcontext ts
     case Map.lookup x lc of
       Nothing -> return a
       Just lti ->
         case varIdentification lti of
           TypeVar _ -> return a
           TermVar _ Nothing -> return a
           TermVar _ (Just d) -> normalize d
             -- shape d >>= normalize 

normalize a@(EigenVar x) = 
  do ts <- get
     let lc = localCxt $ lcontext ts
     case Map.lookup x lc of
       Nothing -> return a
       Just lti ->
         case varIdentification lti of
           TypeVar _ -> return a
           TermVar _ Nothing -> return a
           TermVar _ (Just d) -> normalize d
  

normalize a@(GoalVar x) = return a

normalize a@(Const k) =
  do funPac <- lookupId k
     let f = identification funPac
     case f of
       DataConstr _ -> return a
       DefinedFunction (Just (a, e, e')) ->
         do b <- isBasicValue e
            if b then shape e' else shape a
       DefinedMethod e _ -> shape e
       DefinedInstFunction e _ -> shape e

       
normalize a@(LBase k) = return a

normalize a@(Base k) = return a

normalize (Force' m) =
  do m' <- normalize m 
     case erasePos m' of
       Lift n ->
         shape n >>= normalize
       n -> return (Force' n)

-- normalize (Force m) =
--   do m' <- normalize m 
--      case erasePos m' of
--        Lift n ->
--          normalize n
--        n -> return (Force n)

normalize (App' m n) =
  do m' <- normalize m
     n' <- normalize n
     case m' of
       Lam' bd -> 
         open bd $ \ xs b ->
         let x = head xs in 
         case tail xs of
           [] -> normalize $ apply [(x, n')] b
           t -> return $ Lam' (abst t (apply [(x, n')] b)) 
       _ -> return $ App' m' n'

normalize (AppDep' m n) =
  do m' <- normalize m
     n' <- normalize n
     case m' of
       LamDep' bd -> 
         open bd $ \ xs b ->
         let x = head xs in 
         case tail xs of
           [] -> normalize $ apply [(x, n')] b
           t -> return $ LamDep' (abst t (apply [(x, n')] b)) 
       _ -> return $ AppDep' m' n'

normalize (AppDict m n) =
  do m' <- normalize m
     n' <- normalize n
     case m' of
       LamDict bd -> 
         open bd $ \ xs b ->
         let x = head xs in 
         case tail xs of
           [] -> normalize $ apply [(x, n')] b
           t -> return $ LamDict (abst t (apply [(x, n')] b)) 
       _ -> return $ AppDict m' n'

normalize (AppType m n) =
  do m' <- normalize m
     n' <- normalize n
     case m' of
       LamType bd -> 
         open bd $ \ xs b ->
         let x = head xs in 
         case tail xs of
           [] -> normalize $ apply [(x, n')] b
           t -> return $ LamType (abst t (apply [(x, n')] b)) 
       _ -> return $ AppType m' n'

normalize (AppTm m n) =
  do m' <- normalize m
     n' <- normalize n
     case m' of
       LamTm bd -> 
         open bd $ \ xs b ->
         let x = head xs in 
         case tail xs of
           [] -> normalize $ apply [(x, n')] b
           t -> return $ LamTm (abst t (apply [(x, n')] b)) 
       _ -> return $ AppTm m' n'


normalize (Pair m n) = 
  do v <- normalize m 
     w <- normalize n 
     return (Pair v w)

normalize (Pack m n) = 
  do v <- normalize m 
     w <- normalize n 
     return (Pack v w)

normalize (Circ m n) = 
  do v <- normalize m 
     w <- normalize n 
     return (Circ v w)

normalize (Arrow' m n) = 
  do v <- normalize m 
     w <- normalize n 
     return (Arrow' v w)

normalize (Arrow m n) = 
  do v <- normalize m 
     w <- normalize n 
     return (Arrow v w)

normalize a@(Forall _ _) = return a
normalize a@(Pi _ _) = return a
normalize a@(Pi' _ _) = return a

normalize a@(Exists _ _) = return a

normalize (Let m bd) =
  do m' <- normalize m 
     open bd $ \ x n ->
       let n' = apply [(x, m')] n in normalize n' 

normalize (LetPair m (Abst xs n))  =
  do m' <- normalize m 
     let r = unPair (length xs) m'
     case r of
       Just vs -> 
         let n' = apply (zip xs vs) n
         in normalize n' 
       Nothing -> return (LetPair m' (abst xs n))


normalize (LetPat m bd) =
  do m' <- normalize m 
     case flatten m' of
       Nothing -> return (LetPat m' bd)
       Just (Left id, args) ->
         open bd $ \ p m ->
         case p of
           PApp kid vs
             | kid == id ->
               let m' = helper args vs m in normalize m'
                 -- let vs' = map (\ (Right x) -> x) vs
                 --     subs = (zip vs' args)
                 --     m' = apply subs m
                 -- in normalize m'
           p -> error "from normalize letpat"
  where helper (a:args) ((Right x):vs) m =
          helper args vs (apply [(x, a)] m)
        helper (a:args) ((Left (NoBind t)):vs) m =
          helper args vs m
        helper [] [] m = m
        
normalize b@(Unit) = return b
normalize b@(Set)  = return b
normalize b@(Star) = return b
normalize b@(Box) = return b
normalize b@(Revert) = return b
normalize b@(ExBox) = return b
normalize b@(UnBox) = return b

normalize (Tensor e1 e2) =
  do e1' <- normalize e1 
     e2' <- normalize e2
     return (Tensor e1' e2')

normalize (Imply [] e2) =
  do e2' <- normalize e2 
     return $ Imply [] e2'
     
normalize (Imply (e1:es) e2) =
  do e1' <- normalize e1 
     e' <- normalize (Imply es e2) 
     case e' of
       Imply es' e2' ->
         return (Imply (e1':es') e2')
--       _ ->  return (Imply [e1'] e')
     
normalize (Bang e) =
  do e' <- normalize e 
     return (Bang e')

normalize b@(Case m (B bd)) =
  do m' <- normalize m
     case flatten m' of
       Nothing -> return (Case m' (B bd))
       Just (Left id, args) ->
         reduce id args bd m' 
  where
        reduce id args (bd:bds) m' =
          open bd $ \ p m ->
          case p of
             PApp kid vs
               | kid == id -> let m' = helper args vs m in normalize m' 
                  -- let vs' = map (\ (Right x) -> x) vs
                  --     subs = (zip vs' args)
                  --     m' = apply subs m
                  -- in normalize m' 
               | otherwise -> reduce id args bds m' 
        reduce id args [] m' = throwError $ MissBrErr m' b 

        helper (a:args) ((Right x):vs) m =
          helper args vs (apply [(x, a)] m)
        helper (a:args) ((Left (NoBind t)):vs) m =
          helper args vs m
        helper [] [] m = m
normalize a@(Lift _) = return a
normalize a@(Lam' _) = return a
normalize a@(Lam _) = return a
normalize a@(LamDep' _) = return a
normalize a@(LamDep _) = return a
normalize a@(LamDict _) = return a
normalize a@(LamType _) = return a
normalize a@(LamTm _) = return a
normalize (Pos _ e) = normalize e 
normalize a = error $ "from normalize: " ++ (show $ disp a)


