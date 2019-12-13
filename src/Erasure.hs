{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
module Erasure where

import Syntax
import Nominal
import Utils
import TCMonad

import Control.Monad.Except
import Control.Monad.State
import Debug.Trace
import Text.PrettyPrint
import qualified Data.Set as S

-- | The 'erasure' function erases all the type annotations from the annotated term.


erasure :: Exp -> TCMonad Exp
erasure (Pos p a) = erasure a
erasure Star = return Star
erasure Set = return Set
erasure a@(Var x) = return a
erasure a@(EigenVar x) = return a
erasure a@(GoalVar x) = return a
erasure a@(Const t) = return a 
erasure (App e1 e2) =
  do e1' <- erasure e1
     e2' <- erasure e2
     return $ App e1' e2'

erasure (App' e1 e2) =
  do e1' <- erasure e1
     e2' <- erasure e2
     return $ App' e1' e2'

erasure (AppDict e1 e2) =
  do e1' <- erasure e1
     e2' <- erasure e2
     return $ AppDict e1' e2'

erasure (AppDep e1 e2) =
  do e1' <- erasure e1
     e2' <- erasure e2
     return $ AppDep e1' e2'

erasure (AppDep' e1 e2) =
  do e1' <- erasure e1
     e2' <- erasure e2
     return $ AppDep' e1' e2'

erasure (Pair e1 e2) =
  do e1' <- erasure e1
     e2' <- erasure e2
     return $ Pair e1' e2'

erasure (Circ e1 e2) =
  do e1' <- erasure e1
     e2' <- erasure e2
     return $ Circ e1' e2'

erasure (Pack e1 e2) =
  do e1' <- erasure e1
     e2' <- erasure e2
     return $ Pair e1' e2'

erasure (AppType e1 e2) = erasure e1

erasure (AppTm e1 e2) = erasure e1

erasure a@(Lam (Abst xs m)) =
  do m' <- erasure m
     return $ Lam (abst xs m') 

erasure a@(Lam' (Abst xs m)) =
  do m' <- erasure m
     return $ Lam (abst xs m')

erasure a@(LamDict (Abst xs m)) =
  do m' <- erasure m
     return $ LamDict (abst xs m') 

erasure (LamDep (Abst ys m)) =
  do m' <- erasure m
     return $ LamDep (abst xs m') 


erasure (LamDep' (Abst ys m)) =
  do m' <- erasure m
     return $ LamDep' (abst xs m') 

erasure (LamTm bd) =
  open bd $ \ xs m -> erasure m

erasure (LamType bd) =
  open bd $ \ xs m -> erasure m

erasure (Lift t) =  Lift $ erasure t

erasure (Force t) = Force $ erasure t
erasure (Force' t) = Force' $ erasure t

erasure (UnBox) = UnBox

erasure (Revert) = Revert
erasure (RunCirc) = RunCirc

erasure a@(Box) = a
erasure a@(ExBox) = a

erasure (Let m bd) = open bd $ \ vs b -> 
  do m' <- erasure m
     b' <- erasure b
     return $ Let m' (abst vs b') 
     
erasure (LetPair m bd) = open bd $ \ xs b ->
  do m' <- erasure m
     b' <- erasure b
     return $ LetPair m' (abst xs b') 

erasure (LetEx m bd) = open bd $ \ (x, y) b ->
  do m' <- erasure m
     b' <- erasure b
     return $ LetPair m' (abst [x,y] b')
     
erasure (LetPat m bd) = open bd $ \ pa b ->
  case pa of
    PApp kid args ->
      do b' <- erasure b
         m' <- erasure m
         funP <- lookupConst kid
         isSemi <- querySemiSimple kid
         let ty = classifier funP
         args' <- helper isSemi ty args b 
         return $ LetPat m' (abst (PApp kid args') b')
  where 
        -- The only way a data constructor can have a Pi type
        -- is when it is an existential type. 
        helper flag (Pi bds t) args b | not (isKind t) =
          open bds $ \ ys m ->
          do let (vs, res) = splitAt (length ys) args
             vs' <- helper flag m res b
             return $ vs++vs'

        helper flag (Forall bds t) args b | isKind t =
          open bds $ \ ys m ->
          helper flag m args b

        helper True (Forall bds t) args b =
          open bds $ \ ys m ->
          let (vs, res) = splitAt (length ys) args in
              helper True m res b

        helper False (Forall bds t) args b =
          open bds $ \ ys m ->
          helper False m args b

        helper flag (Arrow t1 t2) (x:xs) b =
          do vs' <- helper flag t2 xs b
             return $ x:vs'

        helper flag (Imply [t1] t2) (x:xs) b =
          do vs' <- helper flag t2 xs b
             return $ x:vs'

        helper flag (Imply (t1:ts) t2) (x:xs) b =
          do vs' <- helper flag (Imply ts t2) xs b
             return $ x:vs'

        helper flag a [] b = return []
        helper flag a _ b = error $ "from helper erasure-letPat"

             


erasure l@(Case e (B br)) =
  do e' <- erasure e
     brs <- mapM helper br
     return $ Case e' (B brs)
       where helper bd = open bd $ \ p m ->
               case p of
                 PApp kid args ->
                   do funP <- lookupConst kid
                      let ty = classifier funP
                      isSemi <- querySemiSimple kid
                      args' <- helper2 isSemi ty args m 
                      m' <- erasure m
                      return (abst (PApp kid args') m')
             -- The only way a data constructor can have a Pi type
             -- is when it is an existential type. 
                      
             helper2 flag (Pi bds t) args ann | not (isKind t) =
               open bds $ \ ys m ->
               do let (vs, res) = splitAt (length ys) args
                  vs' <- helper2 flag m res ann
                  return $ vs++vs'
             helper2 flag (Forall bds t) args ann | isKind t =
               open bds $ \ ys m ->
               helper2 flag m args ann                  
             helper2 True (Forall bds t) args ann =
               open bds $ \ ys m ->
               let (vs, res) = splitAt (length ys) args
               in helper2 True m res ann
             helper2 False (Forall bds t) args ann =
               open bds $ \ ys m ->
               helper2 False m args ann                  
                  
             helper2 flag (Arrow t1 t2) (x:xs) ann =
               do vs' <- helper2 flag t2 xs ann
                  return $ x:vs'
             helper2 flag (Imply [t1] t2) (x:xs) ann =
               do vs' <- helper2 flag t2 xs ann
                  return $ x:vs'

             helper2 flag (Imply (t1:ts) t2) (x:xs) ann =
               do vs' <- helper2 flag (Imply ts t2) xs ann
                  return $ x:vs'
                  
             helper2 flag a [] _ = return []
             helper2 flag a b _ = error $ "from helper2 flag-erasure-case" ++ (show $ disp a)

erasure a@(Wired _) = return a
erasure a = error $ "from erasure" ++ (show $ disp a)


