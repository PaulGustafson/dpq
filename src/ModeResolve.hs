{-# LANGUAGE FlexibleInstances #-}
module ModeResolve where

import Syntax
import Utils
import Substitution

import Control.Monad
import Nominal
import Text.PrettyPrint
import Data.List
import Prelude hiding((<>))

modeResolution m1 DummyM = Just ([], [], [])
modeResolution DummyM m2 = Just ([], [], [])
modeResolution (M x1 x2 x3) (M y1 y2 y3) =
  let s1 = modeResolve x1 y1 
      s2 = modeResolve x2 y2
      s3 = modeResolve x3 y3
  in if null s1 then Nothing
     else if null s2 then Nothing
          else if null s3 then Nothing
               else Just (head s1, head s2, head s3)
  
  
modeSubst s DummyM = DummyM
modeSubst (s1, s2, s3) (M e1 e2 e3) = M e1' e2' e3'
  where e1' = bSubst s1 e1
        e2' = bSubst s2 e2
        e3' = bSubst s3 e3

bSubst s a@(BConst _) = a
bSubst s (BVar x) =
  case lookup x s of
    Nothing -> BVar x
    Just e -> e
bSubst s (BAnd e1 e2) = BAnd (bSubst s e1) (bSubst s e2)

type ModeSubst = [(Variable, BExp)]

instance Disp [(Variable, BExp)] where
  display flag l = vcat $ map (\ (x, b) -> (dispRaw x <> text "|->" <> dispRaw b)) l

modeResolve :: BExp -> BExp -> [ModeSubst]
modeResolve e1 e2 = modeResolve' (simplifyB e1) (simplifyB e2)

modeResolve' :: BExp -> BExp -> [ModeSubst]
modeResolve' (BConst x) (BConst y) | x == y = return []
modeResolve' (BConst x) (BConst y) | otherwise = mzero
modeResolve' (BVar x) e = return [(x, e)]
modeResolve' e (BVar x) = return [(x, e)]
modeResolve' (BConst True) (BAnd e1 e2) =
  do s1 <- modeResolve' (BConst True) e1
     s2 <- modeResolve' (BConst True) (bSubst s1 e2)
     return $ mergeModeSubst s2 s1
modeResolve' (BAnd e1 e2) (BConst True) =
  do s1 <- modeResolve' (BConst True) e1
     s2 <- modeResolve' (BConst True) (bSubst s1 e2)
     return $ mergeModeSubst s2 s1

modeResolve' (BAnd e1 e2) (BConst False) =
  modeResolve' (BConst False) e1 `mplus` modeResolve' (BConst False) e2


modeResolve' (BConst False) (BAnd e1 e2) =
  modeResolve' (BConst False) e1 `mplus` modeResolve' (BConst False) e2


modeResolve' (BAnd e1 e2) (BAnd e1' e2') =
  do{ s1 <- modeResolve' e1 e1';
      s2 <- modeResolve' (bSubst s1 e2) (bSubst s1 e2');
      return $ mergeModeSubst s2 s1} `mplus`
  do{ s1 <- modeResolve' e1 e2';
      s2 <- modeResolve' (bSubst s1 e2) (bSubst s1 e1');
      return $ mergeModeSubst s2 s1}

mergeModeSubst s1 s2 =
  s1 ++ [ (x, bSubst s1 t) | (x, t)<- s2]


bSubstitute :: (ModeSubst, ModeSubst, ModeSubst) -> Exp -> Exp           
bSubstitute s a@(Var y) = a
bSubstitute s a@(GoalVar y) = a
bSubstitute s a@(EigenVar y) = a
bSubstitute s a@(Base _) = a
bSubstitute s a@(LBase _) = a      
bSubstitute s a@(Unit) = a
bSubstitute s a@(Set) = a
bSubstitute s a@(Sort) = a
bSubstitute s a@(Star) = a
bSubstitute s a@(Const _) = a
bSubstitute s (Arrow t t') =
  let t1' = bSubstitute s t
      t2' = bSubstitute s t'
  in Arrow t1' t2'
bSubstitute s (WithType t t') =
  let t1' = bSubstitute s t
      t2' = bSubstitute s t'
  in WithType t1' t2'     
bSubstitute s (Arrow' t t') =
  let t1' = bSubstitute s t
      t2' = bSubstitute s t'
  in Arrow' t1' t2'  
bSubstitute s (Imply t t') =
  let t1' = map (bSubstitute s) t
      t2' = bSubstitute s t'
  in Imply t1' t2'  
bSubstitute s (Tensor t t') =
  let t1' = bSubstitute s t
      t2' = bSubstitute s t'
  in Tensor t1' t2'
bSubstitute s (Circ t t' m) =
  let t1' = bSubstitute s t
      t2' = bSubstitute s t'
      m' = simplify $ modeSubst s m
  in Circ t1' t2' m'

bSubstitute s (Bang t m) =
  Bang (bSubstitute s t) (simplify $ modeSubst s m)

bSubstitute s (Pi bind t) =
  open bind $
  \ ys m -> Pi (abst ys (bSubstitute s m))
           (bSubstitute s t) 

bSubstitute s (PiImp bind t) =
  open bind $
  \ ys m -> PiImp (abst ys (bSubstitute s m))
           (bSubstitute s t) 

bSubstitute s (Pi' bind t) =
  open bind $
  \ ys m -> Pi' (abst ys (bSubstitute s m))
            (bSubstitute s t) 

bSubstitute s (Exists bind t) =
  open bind $
  \ ys m -> Exists (abst ys (bSubstitute s m))
           (bSubstitute s t) 

bSubstitute s (Forall bind t) =
  open bind $
  \ ys m -> Forall (abst ys (bSubstitute s m))
           (bSubstitute s t) 

bSubstitute s (Mod bind) =
  open bind $
  \ ys m -> Mod (abst ys (bSubstitute s m))


bSubstitute s (App t tm) =
  App (bSubstitute s t) (bSubstitute s tm)

bSubstitute s (App' t tm) =
  App' (bSubstitute s t) (bSubstitute s tm)
  
bSubstitute s (AppType t tm) =
  AppType (bSubstitute s t) (bSubstitute s tm)

bSubstitute s (AppTm t tm) =
  AppTm (bSubstitute s t) (bSubstitute s tm)

bSubstitute s (AppDep t tm) =
  AppDep (bSubstitute s t) (bSubstitute s tm)
bSubstitute s (AppDepTy t tm) =
  AppDepTy (bSubstitute s t) (bSubstitute s tm)
  
bSubstitute s (AppDep' t tm) =
  AppDep' (bSubstitute s t) (bSubstitute s tm)  
bSubstitute s (AppDict t tm) =
  AppDict (bSubstitute s t) (bSubstitute s tm)


bSubstitute s (Pair t tm) =
  Pair (bSubstitute s t) (bSubstitute s tm)

bSubstitute s (Force' t) = Force' (bSubstitute s t)
bSubstitute s (Lift t) = Lift (bSubstitute s t) 

bSubstitute s (Pos p e) = Pos p (bSubstitute s e)
bSubstitute s a@(Case _ _) = a
bSubstitute s a = error ("from bSubstitute: " ++ show (disp a))  


flattenB a@(BConst x) = [a]
flattenB a@(BVar x) = [a]
flattenB (BAnd x y) = flattenB x ++ flattenB y

simplify DummyM = DummyM
simplify (M e1 e2 e3) = M (simplifyB e1) (simplifyB e2) (simplifyB e3)

simplifyB :: BExp -> BExp
simplifyB e =
  let bs = filter (\ x -> x /= BConst True) $ flattenB e
  in if null bs then BConst True else
       case find (\ x -> x == BConst False) bs of
         Just _ -> BConst False
         Nothing -> 
           let bs' = nub bs
               e' = foldr BAnd (head bs') (tail bs')
           in e'
