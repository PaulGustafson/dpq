{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
-- | This module defines the 'erasure' function, it erases
-- an annotated expression to a lambda expression without irrelevant annotations.

module Erasure (erasure) where

import Syntax
import Nominal
import Utils
import TCMonad
import TypeError
import SyntacticOperations

import Control.Monad.Except
import Control.Monad.State
import Debug.Trace
import Text.PrettyPrint
import qualified Data.Set as S
import Debug.Trace


-- | Erase a fully annotated expression to a lambda expression, for
-- runtime evaluation.
-- The erasrue function also checks if an irrelevant variable
-- is used as an explicit argument. 

erasure :: Exp -> TCMonad Exp
erasure (Pos p a) = erasure a `catchError` \ e -> throwError $ collapsePos p e
erasure Star = return Star
erasure Unit = return Unit
erasure Set = return Set
erasure a@(Var x) = return a
erasure a@(EigenVar x) = return a
erasure a@(GoalVar x) = return a
erasure a@(Const t) = return a
erasure a@(Base t) = return a
erasure a@(LBase t) = return a

erasure (App e1 e2) =
  do e1' <- erasure e1
     e2' <- erasure e2
     return $ App e1' e2'

-- Convert app' to app
erasure (App' e1 e2) =
  do e1' <- erasure e1
     e2' <- erasure e2
     return $ App e1' e2'

erasure (AppDict e1 e2) =
  do e1' <- erasure e1
     e2' <- erasure e2
     return $ App e1' e2'

erasure (AppDep e1 e2) =
  do e1' <- erasure e1
     e2' <- erasure e2
     return $ App e1' e2'

erasure (AppDepTy e1 e2) =
  do e1' <- erasure e1
     e2' <- erasure e2
     return $ App e1' e2'

erasure (AppDep' e1 e2) =
  do e1' <- erasure e1
     e2' <- erasure e2
     return $ App e1' e2'

erasure (Pair e1 e2) =
  do e1' <- erasure e1
     e2' <- erasure e2
     return $ Pair e1' e2'

erasure (Circ e1 e2) =
  do e1' <- erasure e1
     e2' <- erasure e2
     return $ Circ e1' e2'

erasure (Tensor e1 e2) =
  do e1' <- erasure e1
     e2' <- erasure e2
     return $ Tensor e1' e2'


erasure (Arrow e1 e2) =
  do e1' <- erasure e1
     e2' <- erasure e2
     return $ Arrow e1' e2'

erasure (AppType e1 e2) = erasure e1

erasure (AppTm e1 e2) = erasure e1

erasure a@(Lam (Abst xs m)) =
  do m' <- erasure m
     let vs = S.toList $ getVars AllowEigen m' `S.difference` (S.fromList xs)
     return $ LamV vs (abst xs m') 

erasure a@(LamAnn _ (Abst xs m)) =
  do m' <- erasure m
     let vs = S.toList $ getVars AllowEigen m' `S.difference` (S.fromList xs)
     return $ LamV vs (abst xs m') 

erasure a@(LamAnn' _ (Abst xs m)) =
  do m' <- erasure m
     let vs = S.toList $ getVars AllowEigen m' `S.difference` (S.fromList xs)
     return $ LamV vs (abst xs m') 

-- Convert lam' to lam
erasure a@(Lam' (Abst xs m)) =
  do m' <- erasure m
     let vs = S.toList $ getVars AllowEigen m' `S.difference` (S.fromList xs)
     return $ LamV vs (abst xs m')

erasure a@(LamDict (Abst xs m)) =
  do m' <- erasure m
     let vs = S.toList $ getVars AllowEigen m' `S.difference` (S.fromList xs)
     return $ LamV vs (abst xs m') 

erasure (WithType ann t) = erasure ann

erasure a@(LamDep (Abst ys m)) =
  do m' <- erasure m
     let vs = S.toList $ getVars AllowEigen m' `S.difference` (S.fromList ys)
     return $ LamV vs (abst ys m') 

erasure a@(LamDepTy (Abst ys m)) =
  do m' <- erasure m
     let vs = S.toList $ getVars AllowEigen m' `S.difference` (S.fromList ys)
     return $ LamV vs (abst ys m') 


erasure a@(LamDep' (Abst ys m)) =
  do m' <- erasure m
     let vs = S.toList $ getVars AllowEigen m' `S.difference` (S.fromList ys)
     return $ LamV vs (abst ys m') 

erasure (LamTm bd) =
  open bd $ \ xs m -> erasure m

erasure (LamType bd) =
  open bd $ \ xs m -> erasure m

erasure (Lift t) =
  do t' <- erasure t
     let vs = S.toList $ getVars AllowEigen t'
     return (LiftV vs t')

erasure (Force t) = Force <$> erasure t
erasure (Force' t) = Force <$> erasure t

erasure (UnBox) = return UnBox

erasure (Revert) = return Revert
erasure (RunCirc) = return RunCirc

erasure a@(Box) = return a
erasure a@(ExBox) = return a

erasure (Let m bd) = open bd $ \ vs b -> 
  do m' <- erasure m
     b' <- erasure b
     return $ Let m' (abst vs b') 
     
erasure (LetPair m bd) = open bd $ \ xs b ->
  do m' <- erasure m
     b' <- erasure b
     return $ LetPair m' (abst xs b') 

erasure (LetPat m bd) = open bd $ \ pa b ->
  case pa of
    PApp kid args ->
      do b' <- erasure b
         m' <- erasure m
         funP <- lookupId kid
         let ty = classifier funP
         args' <- helper ty args b 
         return $ LetPat m' (abst (PApp kid args') b')
  where 
        -- The only way a data constructor can have a Pi type
        -- is when it is an existential type. 
        helper (Pi bds t) args b | not (isKind t) =
          open bds $ \ ys m ->
          do let (vs, res) = splitAt (length ys) args
             vs' <- helper m res b
             return $ vs++vs'

        helper (Forall bds t) args b =
          open bds $ \ ys m ->
          let (vs, res) = splitAt (length ys) args in
          do checkExplicit vs b
             helper m res b

        helper (Arrow t1 t2) (x:xs) b =
          do vs' <- helper t2 xs b
             return $ x:vs'

        helper (Imply [t1] t2) (x:xs) b =
          do vs' <- helper t2 xs b
             return $ x:vs'

        helper (Imply (t1:ts) t2) (x:xs) b =
          do vs' <- helper (Imply ts t2) xs b
             return $ x:vs'

        helper a [] b = return []
        helper a _ b = error $ "from helper erasure-letPat"

             


erasure l@(Case e (B br)) =
  do e' <- erasure e
     brs <- mapM helper br
     return $ Case e' (B brs)
       where helper bd = open bd $ \ p m ->
               case p of
                 PApp kid args ->
                   do funP <- lookupId kid
                      let ty = classifier funP
                      args' <- helper2 ty args m 
                      m' <- erasure m
                      return (abst (PApp kid args') m')
             -- The only way a data constructor can have a Pi type
             -- is when it is an existential type. 
                      
             helper2 (Pi bds t) args ann | not (isKind t) =
               open bds $ \ ys m ->
               do let (vs, res) = splitAt (length ys) args
                  vs' <- helper2 m res ann
                  return $ vs++vs'
             helper2 (Forall bds t) args ann =
               open bds $ \ ys m ->
               let (vs, res) = splitAt (length ys) args
               in do checkExplicit vs ann
                     helper2 m res ann
                  
             helper2 (Arrow t1 t2) (x:xs) ann =
               do vs' <- helper2 t2 xs ann
                  return $ x:vs'
             helper2 (Imply [t1] t2) (x:xs) ann =
               do vs' <- helper2 t2 xs ann
                  return $ x:vs'

             helper2 (Imply (t1:ts) t2) (x:xs) ann =
               do vs' <- helper2 (Imply ts t2) xs ann
                  return $ x:vs'
                  
             helper2 a [] _ = return []
             helper2 a b _ = error $ "from helper2 flag-erasure-case" ++ (show $ disp a)

erasure a = error $ "from erasure: " ++ (show $ disp a)

-- | Check if any irrelavant variables in the list is used explicitly in an expression.
checkExplicit :: [Either (NoBind Exp) Variable] -> Exp -> TCMonad ()
checkExplicit [] ann = return ()
checkExplicit (Left a :xs) ann = checkExplicit xs ann
checkExplicit (Right x :xs) ann =
  do when (isExplicit x ann) $ throwError $ ImplicitCase x ann
     checkExplicit xs ann

