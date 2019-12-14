module Normalize where

import Syntax
import TCMonad
import Utils
import Substitution

import Nominal

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

