{-# LANGUAGE FlexibleInstances #-}
module ModeResolve where

import Syntax
import Utils
import Substitution

import Text.PrettyPrint
import Prelude hiding((<>))

modeResolution m1 DummyM = Just ([], [], [])
modeResolution DummyM m2 = Just ([], [], [])
modeResolution (M x1 x2 x3) (M y1 y2 y3) =
  let s1 = modeResove x1 y1 
      s2 = modeResove x2 y2
      s3 = modeResove x3 y3
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

modeResove :: BExp -> BExp -> [ModeSubst]
modeResove (BConst x) (BConst y) | x == y = [[]]
modeResove (BConst x) (BConst y) | otherwise = []
modeResove (BVar x) e = [[(x, e)]]
modeResove e (BVar x) = [[(x, e)]]
modeResolve (BConst True) (BAnd e1 e2) =
  do s1 <- modeResolve (BConst True) e1
     s2 <- modeResolve (BConst True) e2
     return $ mergeModeSubst s1 s2
modeResolve (BAnd e1 e2) (BConst True) =
  do s1 <- modeResolve (BConst True) e1
     s2 <- modeResolve (BConst True) e2
     return $ mergeModeSubst s1 s2

modeResolve (BAnd e1 e2) (BConst False) =
  do s1 <- modeResolve (BConst False) e1
     s2 <- modeResolve (BConst False) e2
     [s1, s2]

modeResolve (BConst False) (BAnd e1 e2) =
  do s1 <- modeResolve (BConst False) e1
     s2 <- modeResolve (BConst False) e2
     [s1, s2]

modeResolve (BAnd e1 e2) (BAnd e1' e2') =
  do s1 <- modeResolve e1 e1'
     s2 <- modeResolve e2 e2'
     return $ mergeModeSubst s1 s2

mergeModeSubst s1 s2 =
  s1 ++ [ (x, bSubst s1 t) | (x, t)<- s2]
