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

normalize a@(Var x) =

  
normalize a@(Label x) m flag = return (m, a)
normalize a@(EigenVar x) m flag = return (m, a)
normalize a@(GoalVar x) m flag = return (m, a)
-- normalize a@(RealOp x) m flag = return (m, a)
-- normalize a@(RealNum) m flag = return (m, a)
-- normalize a@(WrapR _) m flag = return (m, a)
normalize a@(Const k) m flag =
  do funPac <- lookupConst k
     let f = identification funPac
     case f of
       DataConstr _ -> return (m, a)
       DefinedGate e -> shapeTC e >>= \ x -> return (m, x)
       DefinedFunction e ->
         shapeTC e >>= \ x -> normalize x m flag
--       DefinedImplicit e -> normalize e m flag
       DefinedMethod e ->
         shapeTC e >>= \ x -> normalize x m flag         
         -- normalize (shape e) m flag
       DefinedInstFunction e ->
         shapeTC e >>= \ x -> normalize x m flag
         -- normalize (shape e) m flag
--       DefinedTypeFunction e -> normalize e m flag       
normalize a@(LBase k) m flag =
  do funPac <- lookupConst k
     let f = identification funPac
     case f of
       DataType _ _ (Just e) ->
         if flag then
           return (m, e)
           -- normalize e m flag
         else return (m, a)

normalize a@(Base k) m flag =
  do funPac <- lookupConst k
     let f = identification funPac
     case f of
       DataType _ _ Nothing -> return (m, a)
       DictionaryType _ _ -> return (m, a)
       a -> error $ "from normalize Base " ++ show a

normalize (Force m) circ flag =
  do (circ', m') <- normalize m circ flag
     case m' of
       Lift n -> normalize n circ' flag
       n -> return (circ', Force n)

normalize (Force' m) circ flag =
  do (circ', m') <- normalize m circ flag
     case m' of
       Lift n ->
         shapeTC n >>= \ x -> normalize x circ' flag
       n -> return (circ', Force' n)

normalize (App' m n) circ flag =
  do (circ', m') <- normalize m circ flag
     (circ'', n') <- normalize n circ' flag
     b <- isValue n'
     if b then 
       norm_app App' m' n' circ'' flag
       else return (circ'', App' m' n')

normalize (App m n) circ flag =
  do (circ', m') <- normalize m circ flag
     (circ'', n') <- normalize n circ' flag
     b <- isValue n'
     if b then 
       norm_app App m' n' circ'' flag
       else return (circ'', App m' n')

normalize (AppDep' m n) circ flag =
  do (circ', m') <- normalize m circ flag
     (circ'', n') <- normalize n circ' flag
     b <- isValue n'
     if b then 
       norm_app AppDep' m' n' circ'' flag
       else return (circ'', AppDep' m' n')

normalize (AppDict m n) circ flag =
  do (circ', m') <- normalize m circ flag
     (circ'', n') <- normalize n circ' flag
     b <- isValue n'
     if b then 
       norm_app AppDict m' n' circ'' flag
       else return (circ'', AppDict m' n')

normalize (AppType m n) circ flag =
  do (circ', m') <- normalize m circ flag
     (circ'', n') <- normalize n circ' flag
     b <- isValue n'
     if b then 
       norm_app AppType m' n' circ'' flag
       else return (circ'', AppType m' n')

normalize (AppTm m n) circ flag =
  do (circ', m') <- normalize m circ flag
     (circ'', n') <- normalize n circ' flag
     b <- isValue n'
     if b then 
       norm_app AppTm m' n' circ'' flag
       else return (circ'', AppTm m' n')

-- normalize (AppImp m n) circ flag =
--   do (circ', m') <- normalize m circ flag
--      (circ'', n') <- normalize n circ' flag
--      b <- isValue n'
--      if b then 
--        norm_app m' n' circ'' flag
--        else return (circ'', AppImp m' n')


-- For normalizing Real n
-- normalize (AppImp m n) circ flag =
--   do (circ', m') <- normalize m circ flag
--      (circ'', n') <- normalize n circ' flag
--      return (circ'', AppImp m' n')

normalize (Pair m n) circ flag = 
  do (circ', v) <- normalize m circ flag
     (circ'', w) <- normalize n circ' flag
     return (circ'', Pair v w)

normalize (Circ m n) circ flag = 
  do (circ', v) <- normalize m circ flag
     (circ'', w) <- normalize n circ' flag
     return (circ'', Circ v w)

normalize a@(Wired _) c _ = return (c, a)
normalize a@(RunCirc) c _ = return (c, a)
normalize a@(Forall _ _) c _ = return (c, a)
normalize a@(Forall' _ _) c _ = return (c, a)
normalize a@(Pi _ _) c _ = return (c, a)
normalize a@(PiImp _ _) c _ = return (c, a)
normalize a@(Exists _ _) c _ = return (c, a)



normalize (Let m bd c) circ flag =
  do (circ', m') <- normalize m circ flag
     open bd $ \ x n ->
       do b <- isValue m'
          if b then
            let n' = apply [(x, m')] n in normalize n' circ' flag
            else return (circ', Let m' bd c)

normalize (LetPair m (Abst xs n) cs) circ flag =
  do (circ', m') <- normalize m circ flag
     let r = unPair (length xs) m'
     case r of
       Just vs -> 
         do b <- mapM isValue vs
            if and b then
              let n' = apply (zip xs vs) n
              in normalize n' circ' flag
              else return (circ', LetPair m' (abst xs n) cs)
       Nothing -> error "from Normalize letpair"
         -- throwError $ TupleMismatch xs m'

normalize (LetPat m bd) circ flag =
  do (circ', m') <- normalize m circ flag
     let r = getId m'
     case r of
       Nothing -> return (circ', LetPat m' bd)
       Just (Left id, args) ->
         open bd $ \ p m ->
         case p of
           PApp kid vs
             | kid == id ->
               do bs <- mapM isValue args
                  if and bs then 
                    let vs' = map (\ (Right (x, NoBind c)) -> x) vs
                        subs = (zip vs' args)
                        m' = apply subs m
                    in normalize m' circ' flag
                    else return (circ', LetPat m' bd)
           p -> error "from normalize letpat"
             -- throwError $ PatternMismatch p m'

normalize b@(Unit) circ flag = return (circ, b)
normalize b@(Set) circ flag = return (circ, b)
normalize b@(Star) circ flag = return (circ, b)
normalize b@(Box) circ flag = return (circ, b)
normalize b@(Revert) circ flag = return (circ, b)
normalize b@(ExBox) circ flag = return (circ, b)
normalize b@(UnBox) circ flag = return (circ, b)

normalize (Tensor e1 e2) circ flag =
  do (circ', e1') <- normalize e1 circ flag
     (circ'', e2') <- normalize e2 circ' flag
     return (circ'', Tensor e1' e2')
normalize (Arrow e1 e2) circ flag =
  do (circ', e1') <- normalize e1 circ flag
     (circ'', e2') <- normalize e2 circ' flag
     return (circ'', Arrow e1' e2')
normalize (Arrow' e1 e2) circ flag =
  do (circ', e1') <- normalize e1 circ flag
     (circ'', e2') <- normalize e2 circ' flag
     return (circ'', Arrow' e1' e2')

normalize (Imply [] e2) circ flag =
  do (circ', e2') <- normalize e2 circ flag
     return (circ', e2')
     
normalize (Imply (e1:es) e2) circ flag =
  do (circ', e1') <- normalize e1 circ flag
     (circ'', e') <- normalize (Imply es e2) circ' flag
     case e' of
       Imply es' e2' ->
         return (circ'', Imply (e1':es') e2')
       _ ->  return (circ'', Imply [e1'] e')
     
normalize (Bang e) circ flag =
  do (circ', e') <- normalize e circ flag
     return (circ', Bang e')

normalize b@(Case m (B bd)) circ flag =
  do (circ', m') <- normalize m circ flag
     let res = getId m'
     case res of
       Nothing -> return (circ', Case m' (B bd))
       Just (Left id, args) ->
         do c <- mapM isValue args
            if and c then 
              reduce id args bd m' circ'
              else return (circ', Case m' (B bd))
  where -- dis id args =
        --   text "reducing" <+> text "id" <+> hcat (map disp args)
        -- reduce id args (bd:bds) m' circ' | trace (show $ dis id args) $ False = undefined
        reduce id args (bd:bds) m' circ' =
          open bd $ \ p m ->
          case p of
             PApp kid vs
               | kid == id -> 
                  let vs' = map (\ (Right (x, NoBind c)) -> x) vs
                      subs = (zip vs' args)
                      m' = apply subs m
                  in normalize m' circ' flag
               | otherwise -> reduce id args bds m' circ'
        reduce id args [] m' circ' = throwError $ MissBrErr m' b 

normalize a@(Lift _) circ _ = return (circ, a)
normalize a@(Lam' _) circ _ = return (circ, a)
normalize a@(Lam _ _) circ _ = return (circ, a)
normalize a@(LamDep' _) circ _ = return (circ, a)
normalize a@(LamDict _) circ _ = return (circ, a)
normalize a@(LamType _) circ _ = return (circ, a)
normalize a@(LamTm _) circ _ = return (circ, a)


-- normalize RunCirc circ _ = return (circ, RunCirc)
normalize (Pos _ e) circ flag = normalize e circ flag
normalize a _ _ = error $ "from normalize: " ++ (show $ a)

