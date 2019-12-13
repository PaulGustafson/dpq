module SyntacticOperations where

import Syntax
import Utils

import Nominal

import qualified Data.Set as S

-- | Removing all the vacuous pi quantifiers.
removeVacuousPi :: Exp -> Exp
removeVacuousPi (Pos p e) = removeVacuousPi e
removeVacuousPi (Forall (Abst xs m) ty) =
  Forall (abst xs $ removeVacuousPi m) (removeVacuousPi ty)
removeVacuousPi (Pi (Abst xs m) ty) =
  let fvs = getVars AllowEigen m
      xs' = map (\ x ->
                  if S.member x fvs then
                    Just x
                  else Nothing
                ) xs
      ty' = removeVacuousPi ty
      m' = removeVacuousPi m
  in foldr (\ x y -> case x of
                       Nothing -> Arrow ty' y
                       Just x' -> Pi (abst [x'] y) ty'
           ) m' xs'
     
removeVacuousPi (Arrow ty1 ty2) =
  Arrow (removeVacuousPi ty1) (removeVacuousPi ty2)

removeVacuousPi (Imply ps ty2) =
  Imply ps (removeVacuousPi ty2)

removeVacuousPi (Bang ty) = Bang $ removeVacuousPi ty
removeVacuousPi a = a


data VarSwitch = GetGoal -- ^ Get goal variables only.
  | OnlyEigen  -- ^ Obtain only eigen variables from an expression.
  | AllowEigen  -- ^ Free variables in clude eigen variables
  | NoEigen -- ^ Free variables does not clude eigen variables
  | NoImply -- ^ Does not include the variables that occurs in the type class constraints. 
  | OnlyLabel

getVars :: VarSwitch -> Exp -> S.Set Variable
getVars b a@(EigenVar x) = varSwitch b a
getVars b a@(Var x) = varSwitch b a
getVars b a@(Label x) = varSwitch b a
getVars b a@(GoalVar x) = varSwitch b a
getVars b (Base _) = S.empty
getVars b (LBase _) = S.empty
getVars b (Const _) = S.empty
getVars b (Unit) = S.empty
getVars b (Star) = S.empty
getVars b (Set) = S.empty
getVars b (UnBox) = S.empty
getVars b (Revert) = S.empty
getVars b (RunCirc) = S.empty
getVars b (App t t') =
  getVars b t `S.union` getVars b t'
getVars b (App' t t') =
  getVars b t `S.union` getVars b t'  
getVars b (AppType t t') =
  getVars b t `S.union` getVars b t'
getVars b (AppDep t t') =
  getVars b t `S.union` getVars b t'
getVars b (AppDep' t t') =
  getVars b t `S.union` getVars b t'  
getVars b (AppDict t t') =
  getVars b t `S.union` getVars b t'    
getVars b (AppTm t t') =
  getVars b t `S.union` getVars b t'
  
getVars b (Tensor ty tm) =
  getVars b ty `S.union` getVars b tm
getVars b (Arrow ty tm) =
  getVars b ty `S.union` getVars b tm
getVars b (Arrow' ty tm) =
  getVars b ty `S.union` getVars b tm  
getVars NoImply (Imply ty tm) = getVars NoImply tm
getVars b (Imply ty tm) =
  (S.unions $ map (getVars b) ty) `S.union` getVars b tm  
getVars b (Bang t) = getVars b t
getVars b (Pi bind t) =
  getVars b t `S.union`
  (open bind $ \ xs m -> getVars b m `S.difference` S.fromList xs)
getVars b (Pi' bind t) =
  getVars b t `S.union`
  (open bind $ \ xs m -> getVars b m `S.difference` S.fromList xs)  
getVars b (Exists bind t) =
  getVars b t `S.union`
  (open bind $ \ xs m -> getVars b m `S.difference` S.fromList [xs])
getVars b (Lam bind) =
  open bind $ \ xs m -> getVars b m `S.difference` S.fromList xs
getVars b (Lam' bind) =
  open bind $ \ xs m -> getVars b m `S.difference` S.fromList xs  

getVars b (LamType bind) =
  open bind $ \ xs m -> getVars b m `S.difference` S.fromList xs
getVars b (LamDep bind) =
  open bind $ \ xs m -> getVars b m `S.difference` S.fromList xs
getVars b (LamDep' bind) =
  open bind $ \ xs m -> getVars b m `S.difference` S.fromList xs                          
getVars b (LamTm bind) =
  open bind $ \ xs m -> getVars b m `S.difference` S.fromList xs
getVars b (LamDict bind) =
  open bind $ \ xs m -> getVars b m `S.difference` S.fromList xs                        
                        
getVars b (Forall bind ty) =
  open bind $ \ xs m -> S.union (getVars b m `S.difference` S.fromList xs) (getVars b ty)
                    
getVars b (Circ t u) = S.union (getVars b t) (getVars b u)
getVars b (Pair ty tm) =
  getVars b ty `S.union` getVars b tm
getVars b (Pack ty tm) =
  getVars b ty `S.union` getVars b tm

getVars b (Let t bind) =
  getVars b t `S.union`
  (open bind $ \ x m -> S.delete x (getVars b m))

getVars b (LetPair t bind) =
  getVars b t `S.union`
  (open bind $ \ xs m -> (S.difference (getVars b m) (S.fromList xs)))

getVars b (LetEx t bind) =
  getVars b t `S.union`
  (open bind $ \ (x, y) m -> S.delete y (S.delete x (getVars b m)))

getVars b (LetPat t (Abst ps m)) =
  let (bvs, fvs) = pvar ps in
  (getVars b t `S.union` fvs `S.union` getVars b m)
  `S.difference` bvs
  where pvar (PApp _ []) = (S.empty, S.empty)
        pvar (PApp k ((Right x):xs)) =
          let (bv, fv) = pvar (PApp k xs) in
          (S.insert x bv, fv)
        pvar (PApp k ((Left (NoBind x)):xs)) =
          let (bv, fv) = pvar (PApp k xs)
              fbv = getVars b x
          in (bv, S.union fbv fv)

getVars b (Force t) = getVars b t
getVars b (Force' t) = getVars b t
getVars b (Box) = S.empty
getVars b (ExBox) = S.empty
getVars b (Lift t) = getVars b t
getVars b (Case t (B brs)) =
  getVars b t `S.union` S.unions (map helper brs)
  where helper bind = open bind $ \ ps m ->
          let (bvs, fvs) = pvar ps in
          (fvs `S.union` getVars b m) `S.difference` bvs
        pvar (PApp _ []) = (S.empty, S.empty)
        pvar (PApp k ((Right x):xs)) =
          let (bv, fv) = pvar (PApp k xs) in
          (S.insert x bv, fv)
        pvar (PApp k ((Left (NoBind x)):xs)) =
          let (bv, fv) = pvar (PApp k xs)
              fbv = getVars b x
          in (bv, S.union fbv fv)

getVars b (Wired _) = S.empty
getVars b (Pos p e) = getVars b e
getVars b a = error $ "from getVars  " ++ show (disp a)

varSwitch AllowEigen (EigenVar x) = S.insert x S.empty
varSwitch OnlyEigen (EigenVar x) = S.insert x S.empty
varSwitch NoImply (EigenVar x) = S.insert x S.empty
varSwitch _ (EigenVar x) = S.empty
varSwitch OnlyLabel (Label x) = S.insert x S.empty
varSwitch _ (Label x) = S.empty
varSwitch NoEigen (Var x) = S.insert x S.empty
varSwitch AllowEigen (Var x) = S.insert x S.empty
varSwitch NoImply (Var x) = S.insert x S.empty
varSwitch _ (Var x) = S.empty
varSwitch GetGoal (GoalVar x) = S.insert x S.empty
varSwitch _ (GoalVar x) = S.empty






