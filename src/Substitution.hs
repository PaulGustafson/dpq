{-# LANGUAGE  FlexibleInstances #-}
module Substitution where

import Syntax
import Utils
import SyntacticOperations


import Nominal
import qualified Data.Map as Map
import qualified Data.Set as S
import Data.Map (Map)
import Text.PrettyPrint



type Subst = Map Variable Exp

-- | Display substitution.
instance Disp (Map Variable Exp) where
  display b vs =
    let vs' = Map.toList vs in
    vcat $ map helper vs'
     where helper (x,  t) = display b x <+> text "|->" <+> display b t


           
substitute :: Subst -> Exp -> Exp           
substitute s a@(Label y) = a

substitute s a@(Var y) =
  case Map.lookup y s of
    Nothing -> a
    Just t -> t

substitute s a@(GoalVar y) =
  case Map.lookup y s of
    Nothing -> a
    Just t -> t
    
substitute s a@(EigenVar y) = 
  case Map.lookup y s of
    Nothing -> a
    Just t -> t

substitute s a@(Base _) = a
substitute s a@(LBase _) = a      
substitute s a@(Unit) = a
substitute s a@(Set) = a
substitute s a@(Sort) = a
substitute s a@(Star) = a
substitute s a@(Const _) = a
substitute s (Arrow t t') =
  let t1' = substitute s t
      t2' = substitute s t'
  in Arrow t1' t2'
substitute s (Arrow' t t') =
  let t1' = substitute s t
      t2' = substitute s t'
  in Arrow' t1' t2'  
substitute s (Imply t t') =
  let t1' = map (substitute s) t
      t2' = substitute s t'
  in Imply t1' t2'  
substitute s (Tensor t t') =
  let t1' = substitute s t
      t2' = substitute s t'
  in Tensor t1' t2'
substitute s (Circ t t') =
  let t1' = substitute s t
      t2' = substitute s t'
  in Circ t1' t2'
substitute s (Bang t) = Bang (substitute s t)

substitute s (Pi bind t) =
  open bind $
  \ ys m -> Pi (abst ys (substitute s m))
           (substitute s t) 

substitute s (Pi' bind t) =
  open bind $
  \ ys m -> Pi' (abst ys (substitute s m))
            (substitute s t) 

substitute s (Exists bind t) =
  open bind $
  \ ys m -> Exists (abst ys (substitute s m))
           (substitute s t) 

substitute s (Forall bind t) =
  open bind $
  \ ys m -> Forall (abst ys (substitute s m))
           (substitute s t) 

substitute s (App t tm) =
  App (substitute s t) (substitute s tm)

substitute s (App' t tm) =
  App' (substitute s t) (substitute s tm)
  
substitute s (AppType t tm) =
  AppType (substitute s t) (substitute s tm)

substitute s (AppTm t tm) =
  AppTm (substitute s t) (substitute s tm)

substitute s (AppDep t tm) =
  AppDep (substitute s t) (substitute s tm)
substitute s (AppDep' t tm) =
  AppDep' (substitute s t) (substitute s tm)  
substitute s (AppDict t tm) =
  AppDict (substitute s t) (substitute s tm)

substitute s (Lam bind) =
  open bind $
  \ ys m -> Lam (abst ys (substitute s m)) 

substitute s (Lam' bind) =
  open bind $
  \ ys m -> Lam' (abst ys (substitute s m)) 

substitute s (LamType bind) =
  open bind $
  \ ys m -> LamType (abst ys (substitute s m)) 

substitute s (LamTm bind) =
  open bind $
  \ ys m -> LamTm (abst ys (substitute s m)) 

substitute s (LamDict bind) =
  open bind $
  \ ys m -> LamDict (abst ys (substitute s m)) 


substitute s (LamDep bind) =
  open bind $
  \ ys m -> LamDep (abst ys (substitute s m)) 

substitute s (LamDep' bind) =
  open bind $
  \ ys m -> LamDep' (abst ys (substitute s m)) 

substitute s (Pair t tm) =
  Pair (substitute s t) (substitute s tm)
substitute s (Pack t tm) =
  Pack (substitute s t) (substitute s tm)

substitute s (Force t) = Force (substitute s t)
substitute s (Force' t) = Force' (substitute s t)
substitute s (Lift t) = Lift (substitute s t)
substitute s (UnBox) = UnBox
substitute s (Revert) = Revert
substitute s (RunCirc) = RunCirc
substitute s a@(Box) = a
substitute s a@(ExBox) = a
       
substitute s (Let m bd) =
  let m' = substitute s m in
    open bd $ \ y b -> Let m' (abst y (substitute s b)) 

substitute s (LetPair m bd) =
  let m' = substitute s m in
    open bd $ \ ys b -> LetPair m' (abst ys (substitute s b)) 

substitute s (LetEx m bd) =
  let m' = substitute s m in
    open bd $ \ (y, z) b -> LetEx m' (abst (y, z) (substitute s b)) 


substitute s (LetPat m bd) =
  let m' = substitute s m in
   open bd $ \ (PApp id ps) b ->
   let ps' = map (helper s) ps in 
   LetPat m' (abst (PApp id ps') (substitute s b))
  where helper s (Left (NoBind t)) = Left (NoBind (substitute s t))
        helper s (Right x) = Right x
        
substitute s (Case tm (B br)) =
  Case (substitute s tm) (B (helper' br))
  where helper' br =
          map (\ b -> open b $
                       \ (PApp id ps) m ->
                       let ps' = map (helper s) ps in 
                       abst (PApp id ps') (substitute s m))
          br

        helper s (Left (NoBind t)) = Left (NoBind (substitute s t))
        helper s (Right x) = Right x

substitute s a@(Wired _) = a
substitute s (Pos p e) = Pos p (substitute s e)
substitute s a = error ("from substitute: " ++ show (disp a))  


apply s t = let s' = Map.fromList s in substitute s' t

mergeSub :: Map Variable Exp -> Map Variable Exp -> Map Variable Exp
mergeSub new old =
  new `Map.union` Map.map (substitute new) old


