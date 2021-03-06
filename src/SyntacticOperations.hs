-- | This module defines various of syntactic operations on the abstract syntax.

module SyntacticOperations where

import Syntax
import Utils
import Substitution

import Nominal
import Data.List
import qualified Data.Set as S

-- | Remove all the vacuous pi quantifiers.
removeVacuousPi :: Exp -> Exp
removeVacuousPi (Pos p e) = removeVacuousPi e
removeVacuousPi (Forall (Abst xs m) ty) =
  Forall (abst xs $ removeVacuousPi m) (removeVacuousPi ty)
removeVacuousPi (PiImp (Abst xs m) ty) =
 PiImp (abst xs $ removeVacuousPi m) (removeVacuousPi ty)
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

-- | Detect vacuous forall and implicit quantifications,
-- return a list of vacuous variables, their type
-- and the expression that they should occur in. 
vacuousForall :: Exp -> Maybe (Maybe Position, [Variable], Exp, Exp)
vacuousForall (Arrow t1 t2) =
  case vacuousForall t1 of
    Nothing -> vacuousForall t2
    Just p -> Just p

vacuousForall (Pi (Abst vs m) ty) | isKind ty = vacuousForall m
vacuousForall (Pi (Abst vs m) ty) | otherwise = 
  case vacuousForall ty of
    Nothing -> vacuousForall m
    Just p -> Just p

vacuousForall (PiImp bds ty) =
  open bds $ \ vs m ->
   let fvs = getVars NoImply m
       vs' = S.fromList vs
       p = S.isSubsetOf vs' fvs
   in if p then
        case vacuousForall ty of
          Nothing -> vacuousForall m
          Just p -> Just p
      else let diff = S.toList $ S.difference vs' fvs in
             Just (Nothing, diff, ty, m)

vacuousForall (Imply ts t2) = vacuousForall t2
vacuousForall (Bang t2) = vacuousForall t2
vacuousForall (Forall bds ty) =
  open bds $ \ vs m ->
   let fvs = getVars NoImply m
       vs' = S.fromList vs
       p = S.isSubsetOf vs' fvs
   in if p then
        case vacuousForall ty of
          Nothing -> vacuousForall m
          Just p -> Just p
      else let diff = S.toList $ S.difference vs' fvs in
             Just (Nothing, diff, ty, m)

vacuousForall (Pos p e) =
  case vacuousForall e of
    Nothing -> Nothing
    Just (Nothing, vs, t, m) -> Just (Just p, vs, t, m)
    Just r -> Just r
vacuousForall a = Nothing

-- | Flags for getting various of variables.
data VarSwitch = GetGoal -- ^ Get goal variables only.
  | OnlyEigen  -- ^ Obtain only eigen variables from an expression.
  | AllowEigen  -- ^ Free variables in clude eigen variables
  | NoEigen -- ^ Free variables does not clude eigen variables
  | NoImply -- ^ Does not include the variables that occurs in the type class constraints. 

-- | Get a set of variables from an expression according to the flag.
getVars :: VarSwitch -> Exp -> S.Set Variable
getVars b a@(EigenVar x) = varSwitch b a
getVars b a@(Var x) = varSwitch b a
getVars b a@(GoalVar x) = varSwitch b a
getVars b (Base _) = S.empty
getVars b (LBase _) = S.empty
getVars b (Const _) = S.empty
getVars b (Unit) = S.empty
getVars b (Star) = S.empty
getVars b (Sort) = S.empty
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
getVars b (AppDepTy t t') =
  getVars b t `S.union` getVars b t'  
getVars b (AppDep' t t') =
  getVars b t `S.union` getVars b t'  
getVars b (AppDict t t') =
  getVars b t `S.union` getVars b t'    
getVars b (AppTm t t') =
  getVars b t `S.union` getVars b t'

getVars b (WithType t t') =
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

getVars b (PiImp bind t) =
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
getVars b (LamAnn ty bind) =
  open bind $ \ xs m -> (getVars b m `S.difference` S.fromList xs) `S.union`
                        getVars b ty
getVars b (LamAnn' ty bind) =
  open bind $ \ xs m -> (getVars b m `S.difference` S.fromList xs) `S.union`
                        getVars b ty                        
getVars b (Lam' bind) =
  open bind $ \ xs m -> getVars b m `S.difference` S.fromList xs  

getVars b (LamType bind) =
  open bind $ \ xs m -> getVars b m `S.difference` S.fromList xs
getVars b (LamDep bind) =
  open bind $ \ xs m -> getVars b m `S.difference` S.fromList xs
getVars b (LamDepTy bind) =
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

getVars b (Let t bind) =
  getVars b t `S.union`
  (open bind $ \ x m -> S.delete x (getVars b m))

getVars b (LetPair t bind) =
  getVars b t `S.union`
  (open bind $ \ xs m -> (S.difference (getVars b m) (S.fromList xs)))


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
getVars b (Pos p e) = getVars b e
getVars b a = error $ "from getVars  " ++ show (disp a)

-- | Get variables according to 'VarSwitch'.
varSwitch :: VarSwitch -> Exp -> S.Set Variable
varSwitch AllowEigen (EigenVar x) = S.insert x S.empty
varSwitch OnlyEigen (EigenVar x) = S.insert x S.empty
varSwitch NoImply (EigenVar x) = S.insert x S.empty
varSwitch _ (EigenVar x) = S.empty
varSwitch NoEigen (Var x) = S.insert x S.empty
varSwitch AllowEigen (Var x) = S.insert x S.empty
varSwitch NoImply (Var x) = S.insert x S.empty
varSwitch _ (Var x) = S.empty
varSwitch GetGoal (GoalVar x) = S.insert x S.empty
varSwitch _ (GoalVar x) = S.empty

-- | Flatten a n-tuple into a list.
unPair :: (Num a, Ord a) => a -> Exp -> Maybe [Exp]
unPair n (Pos _ e) = unPair n e
unPair n (Pair x y) | n == 2 = Just [x, y]
unPair n (Pair x y) | n > 2 =
  do r <- unPair (n-1) x
     return (r++[y])
unPair _ _ = Nothing

-- | Flatten a n-value-tuple into a list.
unVPair :: (Num t, Ord t) => t -> Value -> Maybe [Value]
unVPair n (VPair x y) | n == 2 = Just [x, y]
unVPair n (VPair x y) | n > 2 =
  do r <- unVPair (n-1) x
     return (r++[y])
unVPair _ _ = Nothing

-- | Flatten a multi-tensor into a list.
unTensor :: (Num a, Ord a) => a -> Exp -> Maybe [Exp]
unTensor n (Pos _ e) = unTensor n e
unTensor n (Tensor x y) | n == 2 = Just [x, y]
unTensor n (Tensor x y) | n > 2 =
  do r <- unTensor (n-1) x
     return (r++[y])
unTensor _ _ = Nothing

-- | Flatten a type expression into bodies and head, with variables intact.
-- e.g. @flattenArrows ((x :: A1) -> A2 -> (P) => H)@ produces
-- @([(Just x, A1), (Nothing, A2), (Nothing, P)], H)@

flattenArrows :: Exp -> ([(Maybe Variable, Exp)], Exp)
flattenArrows (Pos p a) = flattenArrows a
flattenArrows (Arrow t1 t2) =
  let (res, h) = flattenArrows t2 in
  ((Nothing, t1):res, h)
flattenArrows (Arrow' t1 t2) =
  let (res, h) = flattenArrows t2 in
  ((Nothing, t1):res, h)  
flattenArrows (Pi (Abst vs t2) t1) = 
  let (res, h) = flattenArrows t2 in
  (map (\ x -> (Just x, t1)) vs ++ res, h)
flattenArrows (PiImp (Abst vs t2) t1) = 
  let (res, h) = flattenArrows t2 in
  (map (\ x -> (Just x, t1)) vs ++ res, h)
  
flattenArrows (Pi' (Abst vs t2) t1) = 
  let (res, h) = flattenArrows t2 in
  (map (\ x -> (Just x, t1)) vs ++ res, h)  
flattenArrows (Imply t1 t2) =
  let (res, h) = flattenArrows t2 in
  ((map (\ x -> (Nothing, x)) t1)++ res, h)  
flattenArrows a = ([], a)  


-- | Remove the leading forall quantifiers, and class quantifiers if flag is True.
removePrefixes :: Bool -> Exp -> ([(Maybe Variable, Exp)], Exp)
removePrefixes flag (Forall bd ty) =
  open bd $ \ vs m ->
  let vs' = map (\ x -> (Just x, ty)) vs
      (xs, m') = removePrefixes flag m
  in (vs' ++ xs, m')
removePrefixes flag (Imply bd ty) | flag =
  let vs' = map (\ x -> (Nothing, x)) bd
      (xs, m') = removePrefixes flag ty
  in (vs' ++ xs, m')
removePrefixes flag (Pos _ a) = removePrefixes flag a
removePrefixes flag a = ([], a)

-- | Flatten an applicative expression. It can
-- be applied to both type and term expression. It return 'Nothing' if the input is not
-- in applicative form. 'Left' indicates the identifier is a term constructor, 'Right' 
-- indicates the identifier is a type construtor.
-- It also returns a list of arguments.

flatten :: Exp -> Maybe (Either Id Id, [Exp])
flatten (Base id) = return (Right id, [])
flatten (LBase id) = return (Right id, [])
flatten (Const id) = return (Left id, [])
flatten (App t1 t2) =
  do (id, args) <- flatten t1
     return (id, args ++ [t2])
flatten (App' t1 t2) =
  do (id, args) <- flatten t1
     return (id, args ++ [t2])     
flatten (AppDep t1 t2) =
  do (id, args) <- flatten t1
     return (id, args ++ [t2])
flatten (AppDepTy t1 t2) =
  do (id, args) <- flatten t1
     return (id, args ++ [t2])     
flatten (AppDict t1 t2) =
  do (id, args) <- flatten t1
     return (id, args ++ [t2])          
flatten (AppType t1 t2) =
  do (id, args) <- flatten t1
     return (id, args ++ [t2])          
flatten (AppTm t1 t2) =
  do (id, args) <- flatten t1
     return (id, args ++ [t2])          
flatten (Pos p e) = flatten e
flatten _ = Nothing

-- | Flatten an applicative value. 
vflatten :: Value -> Maybe (Either Id Id, [Value])
vflatten (VBase id) = return (Right id, [])
vflatten (VLBase id) = return (Right id, [])
vflatten (VConst id) = return (Left id, [])
vflatten (VApp t1 t2) =
  do (id, args) <- vflatten t1
     return (id, args ++ [t2])
vflatten _ = Nothing


-- | Determine whether an expression is a kind expression. Note we allow
-- dependent kind such as: @(a :: Type) -> a -> Type@.
isKind :: Exp -> Bool
isKind (Set) = True
isKind (Arrow k1 k2) = isKind k2
isKind (Pi b ty) = open b $ \ vs b' -> isKind b'
isKind (Forall b ty) = open b $ \ vs b' -> isKind b'
isKind (Pos _ e) = isKind e
isKind _ = False

-- | Erase the positions from an expression.
erasePos :: Exp -> Exp
erasePos (Pos _ e) = erasePos e
erasePos (Unit) = Unit
erasePos (Set) = Set
erasePos (Sort) = Sort
erasePos Star = Star
erasePos a@(Var x) = a
erasePos a@(EigenVar x) = a
erasePos a@(GoalVar x) = a
erasePos a@(Base x) = a
erasePos a@(LBase x) = a
erasePos a@(Const x) = a
erasePos (App e1 e2) = App (erasePos e1) (erasePos e2)
erasePos (App' e1 e2) = App' (erasePos e1) (erasePos e2)
erasePos (AppType e1 e2) = AppType (erasePos e1) (erasePos e2)
erasePos (AppTm e1 e2) = AppTm (erasePos e1) (erasePos e2)
erasePos (AppDep e1 e2) = AppDep (erasePos e1) (erasePos e2)
erasePos (AppDepTy e1 e2) = AppDepTy (erasePos e1) (erasePos e2)
erasePos (AppDep' e1 e2) = AppDep' (erasePos e1) (erasePos e2)
erasePos (AppDict e1 e2) = AppDict (erasePos e1) (erasePos e2)
erasePos (Tensor e1 e2) = Tensor (erasePos e1) (erasePos e2)
erasePos (WithType e1 e2) = WithType (erasePos e1) (erasePos e2)
erasePos (Pair e1 e2) = Pair (erasePos e1) (erasePos e2)
erasePos (Arrow e1 e2) = Arrow (erasePos e1) (erasePos e2)
erasePos (Arrow' e1 e2) = Arrow' (erasePos e1) (erasePos e2)
erasePos (Imply e1 e2) = Imply (map erasePos e1) (erasePos e2)
erasePos (Bang e) = Bang $ erasePos e
erasePos (UnBox) = UnBox
erasePos (Revert) = Revert
erasePos (RunCirc) = RunCirc
erasePos (Box) = Box
erasePos a@(ExBox) = a
erasePos (Lift e) = Lift $ erasePos e
erasePos (Force e) = Force $ erasePos e
erasePos (Force' e) = Force' $ erasePos e
erasePos (Circ e1 e2) = Circ (erasePos e1) (erasePos e2)
erasePos (Pi (Abst vs b) e) = Pi (abst vs (erasePos b)) (erasePos e)
erasePos (PiImp (Abst vs b) e) = PiImp (abst vs (erasePos b)) (erasePos e)

erasePos (Pi' (Abst vs b) e) = Pi' (abst vs (erasePos b)) (erasePos e)
erasePos (Exists (Abst vs b) e) = Exists (abst vs (erasePos b)) (erasePos e)
erasePos (Forall (Abst vs b) e) = Forall (abst vs (erasePos b)) (erasePos e)
erasePos (Lam (Abst vs b)) = Lam (abst vs (erasePos b))
erasePos (LamAnn ty (Abst vs b)) = LamAnn (erasePos ty) (abst vs (erasePos b))
erasePos (LamAnn' ty (Abst vs b)) = LamAnn' (erasePos ty) (abst vs (erasePos b))
erasePos (Lam' (Abst vs b)) = Lam' (abst vs (erasePos b)) 
erasePos (LamTm (Abst vs b)) = LamTm (abst vs (erasePos b))
erasePos (LamDep (Abst vs b)) = LamDep (abst vs (erasePos b))
erasePos (LamDepTy (Abst vs b)) = LamDepTy (abst vs (erasePos b)) 
erasePos (LamType (Abst vs b)) = LamType (abst vs (erasePos b))
erasePos (LamDict (Abst vs b)) = LamDict (abst vs (erasePos b))
erasePos (Let m (Abst vs b)) = Let (erasePos m) (abst vs (erasePos b)) 
erasePos (LetPair m (Abst xs b)) = LetPair (erasePos m) (abst xs (erasePos b)) 
erasePos (LetPat m (Abst (PApp id vs) b)) = LetPat (erasePos m) (abst (PApp id vs) (erasePos b))
erasePos (Case e (B br)) = Case (erasePos e) (B (map helper br))
  where helper (Abst p m) = abst p (erasePos m)
erasePos e = error $ "from erasePos " ++ (show $ disp e)

-- | Determine if an expression is an eigenvariable. 
isEigenVar :: Exp -> Bool
isEigenVar (EigenVar _) = True
isEigenVar (Pos p e) = isEigenVar e
isEigenVar _ = False

-- | Determine if an expression is a constructor.
isConst :: Exp -> Bool
isConst (Const _) = True
isConst (Pos p e) = isConst e
isConst _ = False

-- | Determine if a value is a circuit.
isCirc :: Value -> Bool
isCirc (Wired _) = True
isCirc _ = False


-- | Convert all the eigenvariables in an expression to the usual variables.
unEigen :: Exp -> Exp
unEigen = unEigenBound []

-- | Convert all the eigenvariables in an expression to the usual variables,
-- taking the input /vars/ into account.
unEigenBound :: [Variable] -> Exp -> Exp
unEigenBound vars (Pos p e) = Pos p (unEigenBound vars e)
unEigenBound vars (Unit) = Unit
unEigenBound vars (Set) = Set
unEigenBound vars Star = Star
unEigenBound vars a@(Var x) = a
unEigenBound vars a@(GoalVar x) = a
unEigenBound vars a@(EigenVar x) = if x `elem` vars then Var x else a
unEigenBound vars a@(Base x) = a
unEigenBound vars a@(LBase x) = a
unEigenBound vars a@(Const x) = a

unEigenBound vars (App e1 e2) =
  let e1' = (unEigenBound vars e1)
      e2' = (unEigenBound vars e2)
  in App e1' e2'

unEigenBound vars (App' e1 e2) =
  let e1' = (unEigenBound vars e1)
      e2' = (unEigenBound vars e2)
  in App' e1' e2'

unEigenBound vars (WithType e1 e2) =
  let e1' = (unEigenBound vars e1)
      e2' = (unEigenBound vars e2)
  in WithType e1' e2'

unEigenBound vars (AppType e1 e2) =
  let e1' = (unEigenBound vars e1)
      e2' = (unEigenBound vars e2)
  in AppType e1' e2'  

unEigenBound vars (AppTm e1 e2) =
  let e1' = (unEigenBound vars e1)
      e2' = (unEigenBound vars e2)
  in AppTm e1' e2'  

unEigenBound vars (AppDep e1 e2) =
  let e1' = (unEigenBound vars e1)
      e2' = (unEigenBound vars e2)
  in AppDep e1' e2'  

unEigenBound vars (AppDep' e1 e2) =
  let e1' = (unEigenBound vars e1)
      e2' = (unEigenBound vars e2)
  in AppDep' e1' e2'  

unEigenBound vars (AppDepTy e1 e2) =
  let e1' = (unEigenBound vars e1)
      e2' = (unEigenBound vars e2)
  in AppDepTy e1' e2'  

unEigenBound vars (AppDict e1 e2) =
  let e1' = (unEigenBound vars e1)
      e2' = (unEigenBound vars e2)
  in AppDict e1' e2'  

unEigenBound vars (Tensor e1 e2) =
  let e1' = (unEigenBound vars e1)
      e2' = (unEigenBound vars e2)
  in Tensor e1' e2'
  
unEigenBound vars (Pair e1 e2) = 
  let e1' = (unEigenBound vars e1)
      e2' = (unEigenBound vars e2)
  in  Pair e1' e2'

unEigenBound vars (Arrow e1 e2) =
  let e1' = (unEigenBound vars e1)
      e2' = (unEigenBound vars e2)
  in Arrow e1' e2'

unEigenBound vars (Arrow' e1 e2) =
  let e1' = (unEigenBound vars e1)
      e2' = (unEigenBound vars e2)
  in Arrow' e1' e2'

unEigenBound vars (Imply e1 e2) =
  let e1' = map (unEigenBound vars) e1
      e2' = unEigenBound vars e2
  in Imply e1' e2'

unEigenBound vars (Bang e) = Bang (unEigenBound vars e)
unEigenBound vars (UnBox) = UnBox
unEigenBound vars (Revert) = Revert
unEigenBound vars (RunCirc) = RunCirc
unEigenBound vars (Box) = Box 
unEigenBound vars (ExBox) = ExBox 
unEigenBound vars (Lift e) = Lift (unEigenBound vars e)
unEigenBound vars (Force e) = Force (unEigenBound vars e)
unEigenBound vars (Force' e) = Force' (unEigenBound vars e)

unEigenBound vars (Circ e1 e2) =
  let e1' = (unEigenBound vars e1)
      e2' = (unEigenBound vars e2)
  in Circ e1' e2'

unEigenBound vars (LetPair m bd) = open bd $ \ xs b ->
  let m' = (unEigenBound vars m)
      b' = (unEigenBound (xs ++ vars) b)
  in LetPair m' (abst xs b') 

unEigenBound vars (LetPat m bd) = open bd $ \ (PApp id vs) b ->
  let m' = unEigenBound vars m
      (bvs, vs') = pvar vs
      b' = unEigenBound (bvs ++ vars) b
  in LetPat m' (abst (PApp id vs') b')
 where  pvar ([]) = ([], [])

        pvar (Right x : xs) =
          let (bv, fv) = pvar xs in
          (x:bv, Right x : fv)

        pvar (Left (NoBind (Var x)):xs) =
          let (bv, fv) = pvar xs in
          if x `elem` vars then
            (bv, Left (NoBind (Var x)):fv)
          else (x:bv, Right x : fv)

        pvar (Left (NoBind (EigenVar x)):xs) =
          let (bv, fv) = pvar xs in
          if x `elem` vars then
            (bv, Left (NoBind (Var x)):fv)
          else (x:bv, Right x : fv)
          
        pvar ((Left (NoBind x)):xs) =
          let (bv, fv) = pvar xs
              x' = unEigenBound vars x
          in (bv, Left (NoBind x'):fv)
   
unEigenBound vars (Let m bd) = open bd $ \ p b ->
  let m' = (unEigenBound vars m)
      b' = (unEigenBound (p:vars) b)
  in Let m' (abst p b') 

unEigenBound vars (LamTm bd) =
  open bd $ \ xs m ->
   let m' = unEigenBound (xs ++ vars) m
   in LamTm $ abst xs m'

unEigenBound vars (LamDep bd) =
  open bd $ \ xs m ->
   let m' = unEigenBound (xs ++ vars) m
   in LamDep (abst xs m') 

unEigenBound vars (LamDepTy bd) =
  open bd $ \ xs m ->
   let m' = unEigenBound (xs ++ vars) m
   in LamDepTy (abst xs m') 

unEigenBound vars (LamDep' bd) =
  open bd $ \ xs m ->
   let m' = unEigenBound (xs ++ vars) m
   in LamDep' (abst xs m') 

unEigenBound vars (Lam bd) =
  open bd $ \ xs m ->
   let m' = unEigenBound (xs ++ vars) m
   in Lam (abst xs m') 

unEigenBound vars (LamAnn ty bd) =
  open bd $ \ xs m ->
   let m' = unEigenBound (xs ++ vars) m
       ty' = unEigenBound vars ty
   in LamAnn ty' (abst xs m') 

unEigenBound vars (LamAnn' ty bd) =
  open bd $ \ xs m ->
   let m' = unEigenBound (xs ++ vars) m
       ty' = unEigenBound vars ty
   in LamAnn' ty' (abst xs m') 

unEigenBound vars (Lam' bd) =
  open bd $ \ xs m ->
   let m' = unEigenBound (xs ++ vars) m
   in Lam' (abst xs m') 

unEigenBound vars (LamType bd) =
  open bd $ \ xs m ->
   let m' = unEigenBound (xs ++ vars) m
   in LamType $ abst xs m'

unEigenBound vars (LamDict bd) =
  open bd $ \ xs m ->
   let m' = unEigenBound (xs ++ vars) m
   in LamDict $ abst xs m'

unEigenBound vars (Pi bd ty) =
  open bd $ \ xs m ->
   let m' = unEigenBound (xs ++ vars) m
       ty' = unEigenBound vars ty
   in Pi (abst xs m') ty'

unEigenBound vars (PiImp bd ty) =
  open bd $ \ xs m ->
   let m' = unEigenBound (xs ++ vars) m
       ty' = unEigenBound vars ty
   in PiImp (abst xs m') ty'

unEigenBound vars (Pi' bd ty) =
  open bd $ \ xs m ->
   let m' = unEigenBound (xs ++ vars) m
       ty' = unEigenBound vars ty
   in Pi' (abst xs m') ty'

unEigenBound vars (Exists bd ty) =
  open bd $ \ xs m ->
   let m' = unEigenBound (xs:vars) m
       ty' = unEigenBound vars ty
   in Exists (abst xs m') ty'

unEigenBound vars (Forall bd ty) =
  open bd $ \ xs m ->
   let m' = unEigenBound (xs ++ vars) m
       ty' = unEigenBound vars ty
   in Forall (abst xs m') ty'

      
unEigenBound vars a@(Case e (B br)) =
  let e' = unEigenBound vars e
      br' = map helper br
  in Case e' (B br')
  where helper b = open b $ \ (PApp id vs) b ->
          let (bvs, vs') = pvar vs in
          abst (PApp id vs') (unEigenBound (bvs ++vars) b)

        pvar ([]) = ([], [])

        pvar ((Right x):xs) =
          let (bv, fv) = pvar xs in
          (x:bv, (Right x):fv)

        pvar ((Left (NoBind (Var x))):xs) =
          let (bv, fv) = pvar xs in
          if x `elem` vars then
            (bv, (Left (NoBind (Var x))):fv)
          else (x:bv, (Right x):fv)

        pvar ((Left (NoBind (EigenVar x))):xs) =
          let (bv, fv) = pvar xs in
          if x `elem` vars then
            (bv, (Left (NoBind (Var x))):fv)
          else (x:bv, (Right x):fv)

        pvar ((Left (NoBind x)):xs) =
          let (bv, fv) = pvar xs
              x' = unEigenBound vars x
          in (bv, (Left (NoBind x')):fv)
unEigenBound vars a = error $ "from unEigenBound" ++ (show $ disp a)

-- | Flags for the 'unwind' function.
data UnwindFlag = AppFlag | App'Flag | AppDep'Flag
                | AppDepFlag | AppDictFlag 
  deriving (Show, Eq)


-- | Unwind an applicative depending on the 'UnwindFlag'.
unwind a (Pos _ e) = unwind a e

unwind a@(AppFlag) (App t1 t2) =
  unwindHelper a t1 t2

unwind a@(App'Flag) (App' t1 t2) =
  unwindHelper a t1 t2

unwind a@(AppDep'Flag) (AppDep' t1 t2) =
  unwindHelper a t1 t2

unwind a@(AppDepFlag) (AppDep t1 t2) =
  unwindHelper a t1 t2

unwind a@(AppDictFlag) (AppDict t1 t2) =
  unwindHelper a t1 t2

unwind _ b = (b, [])

-- | Unwind application. A helper function for 'unwind'.
unwindHelper :: UnwindFlag -> Exp -> Exp -> (Exp, [Exp])
unwindHelper a t1 t2 =
  let (h, args) = unwind a t1
   in (h, args++[t2])
      

-- | Obtain a position information if the expression has one at the top level.
obtainPos :: Exp -> Maybe Position
obtainPos (Pos p e) = Just p
obtainPos _ = Nothing

-- | Obtain the labels from a simple term.
getWires :: Value -> [Label]
getWires (VLabel x) = [x]
getWires (VConst _) = []
getWires VStar = []
getWires (VApp e1 e2) = getWires e1 ++ getWires e2
getWires (VPair e1 e2) = getWires e1 ++ getWires e2
getWires a = error $ "applying getWires function to an ill-formed template:" ++ (show $ disp a)


-- | Check if a variable is used explicitly for runtime evaluation.
isExplicit :: Variable -> Exp -> Bool
isExplicit s (App t tm) =
   (isExplicit s t) || (isExplicit s tm)

isExplicit s (WithType t tm) =
  (isExplicit s t) 

isExplicit s (Arrow t tm) =
   (isExplicit s t) || (isExplicit s tm)

isExplicit s (App' t tm) =
   (isExplicit s t) || (isExplicit s tm)

isExplicit s (AppType t tm) =
  (isExplicit s t)
isExplicit s (AppTm t tm) =
   (isExplicit s t)

isExplicit s (AppDep t tm) =
   (isExplicit s t) || (isExplicit s tm)

isExplicit s (AppDepTy t tm) =
   (isExplicit s t) || (isExplicit s tm)

isExplicit s (AppDep' t tm) =
   (isExplicit s t) || (isExplicit s tm)

isExplicit s (AppDict t tm) =
   (isExplicit s t) || (isExplicit s tm)

isExplicit s (Lam bind) =
  open bind $
  \ ys m -> isExplicit s m

isExplicit s (LamAnn ty bind) =
  open bind $
  \ ys m -> isExplicit s m
isExplicit s (LamAnn' ty bind) =
  open bind $
  \ ys m -> isExplicit s m

isExplicit s (LamDict bind) =
  open bind $
  \ ys m -> isExplicit s m

isExplicit s (Lam' bind) =
  open bind $
  \ ys m -> isExplicit s m

isExplicit s (LamType bind) =
  open bind $
  \ ys m -> isExplicit s m 

isExplicit s (LamTm bind) =
  open bind $
  \ ys m -> isExplicit s m

isExplicit s (LamDep bind) =
  open bind $
  \ ys m -> isExplicit s m

isExplicit s (LamDepTy bind) =
  open bind $
  \ ys m -> isExplicit s m

isExplicit s (Pair t tm) =
   (isExplicit s t) || (isExplicit s tm)

isExplicit s (Tensor t tm) =
   (isExplicit s t) || (isExplicit s tm)
   
isExplicit s (Force t) = (isExplicit s t)
isExplicit s (Force' t) = (isExplicit s t)
isExplicit s (Lift t) = (isExplicit s t)
       
isExplicit s (Let m bd) =
  if isExplicit s m then True
  else open bd $ \ y b -> isExplicit s b

isExplicit s (LetPair m bd) =
  if isExplicit s m then True
  else 
    open bd $ \ ys b -> isExplicit s b

isExplicit s (LetPat m bd) =
  if isExplicit s m then True
  else open bd $ \ ps b ->  isExplicit s b

isExplicit s (Case tm (B br)) =
  if isExplicit s tm then True
  else or (helper' br)
  where helper' ps =
          map (\ b -> open b $
                       \ ys m ->
                        (isExplicit s m))
          ps

isExplicit s (Pos p e) = isExplicit s e
isExplicit s (Var x) = s == x 
isExplicit s (EigenVar x) = s == x 
isExplicit s Star = False
isExplicit s Box = False
isExplicit s UnBox = False
isExplicit s ExBox = False
isExplicit s Revert = False
isExplicit s Unit = False
isExplicit s Set = False
isExplicit s (Base _) = False
isExplicit s (LBase _) = False
isExplicit s (Const _) = False

isExplicit s a = error $ "from isExplicit:" ++ (show $ disp a)

-- | Convert all the free variables in an expression into eigenvariables.
toEigen :: Exp -> Exp
toEigen t =
  let fvs = S.toList $ getVars NoEigen t
      sub = zip fvs (map EigenVar fvs)
  in apply sub t

-- | Count the number of gates in a circuit.
gateCount Nothing (Wired (Abst _ (VCircuit (Morphism _ gs _)))) = genericLength gs
gateCount (Just n) (Wired (Abst _ (VCircuit (Morphism _ gs _)))) =
  helper n gs 0
  where helper n [] m = m
        helper n (Gate d _ _ _ _:s) m
          | getName d == n = helper n s (m+1)
          | otherwise = helper n s m
        

