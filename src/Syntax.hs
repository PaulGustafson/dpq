{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleInstances, RankNTypes, GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass, PatternSynonyms, ViewPatterns #-}

{-|
We use the nominal library provided by Peter Selinger.
Please see <http://hackage.haskell.org/package/nominal here> for
its documentation.
-}
module Syntax where

import Utils

import Prelude hiding ((.), (<>))


import Nominal
import Nominal.Atom
import Nominal.Atomic

import Control.Monad.Identity
import Control.Monad.Except
import Text.PrettyPrint
import qualified Data.Map as Map
import qualified Data.Set as S
import Data.Map (Map)

import Data.List
import Debug.Trace



data V

instance AtomKind V where
  suggested_names _ = ["a", "b", "c", "d", "e", "x", "y", "z"]
  expand_names _ xs = xs ++ [ x ++ (show n) | n <- [1..], x <- xs ]

data Variable = Variable (AtomOfKind V) (NoBind String) 
  deriving (Generic, Bindable, Nominal, NominalShow, NominalSupport, Ord)

instance NominalShow (NoBind String) where
  showsPrecSup sup d (NoBind x) = showsPrecSup sup d x

instance NominalShow (NoBind Exp) where
  showsPrecSup sup d (NoBind x) = showsPrecSup sup d x
   
instance Show Variable where
  show (Variable a _) = show a

instance Eq Variable where
  (Variable x _) == (Variable y _) = x == y
  
instance Disp Variable where
  display True (Variable x (NoBind y)) = text y
  display False (Variable x _) = text (show x)
  
pattern Abst :: (Bindable a, Nominal t) => a -> t -> Bind a t
pattern Abst x t <- ((\ b -> open b (\ x b' -> (x, b'))) -> (x, t))


freshNames :: [String] -> ([Variable] -> t) -> t
freshNames [] body = body []
freshNames (n:ns) body =
  freshName n $ \ a ->
  freshNames ns $ \ as ->
  body (a:as)
  where freshName s k =
          with_fresh $ \a -> k (Variable a (NoBind s))

data Exp =
  Var Variable
  | Label Variable
  | EigenVar Variable
  | GoalVar Variable 
  | Const Id
  | LBase Id
  | Base Id 
  | Lam (Bind [Variable] Exp) 
  | Lam' (Bind [Variable] Exp)
  | App Exp Exp
  | App' Exp Exp 
  | AppDict Exp Exp
  | Pair Exp Exp
  | Pack Exp Exp
  | Let Exp (Bind Variable Exp) 
  | LetPair Exp (Bind [Variable] Exp)
  | LetEx Exp (Bind (Variable, Variable) Exp) 
  | LetPat Exp (Bind Pattern Exp) 
  | Star
  | Force Exp
  | Force' Exp
  | Lift Exp
  | Box
  | ExBox
  | UnBox
  | RunCirc
  | Revert 
  | Case Exp Branches
  | Arrow Exp Exp
  | Arrow' Exp Exp
  | Imply [Exp] Exp
  | Tensor Exp Exp 
  | Unit
  | Set 
  | Sort
  | Bang Exp
  | Circ Exp Exp
  | Pi (Bind [Variable] Exp) Exp
  | Pi' (Bind [Variable] Exp) Exp
  | Exists (Bind Variable Exp) Exp
  | Forall (Bind [Variable] Exp) Exp
  | Wired (Bind [Variable] Morphism)
  | LamType (Bind [Variable] Exp)
  | LamTm (Bind [Variable] Exp)
  | LamDict (Bind [Variable] Exp)
  | LamDep (Bind [Variable] Exp)
  | LamDep' (Bind [Variable] Exp)
  | AppType Exp Exp 
  | AppTm Exp Exp  
  | AppDep Exp Exp 
  | AppDep' Exp Exp
  | PlaceHolder
  | Pos Position Exp
  deriving (Eq, Generic, Nominal, NominalShow, NominalSupport, Show)


-- | Gate <name> <params> <in> <out> <ctrls>
data Gate = Gate Id [Exp] Exp Exp Exp
          deriving (Eq, Generic, NominalSupport, NominalShow, Nominal)

type Gates = [Gate]

-- | (a, Cs, b)
data Morphism = Morphism Exp Gates Exp
              deriving (Eq, Generic, NominalSupport, NominalShow, Nominal)

data Branches = B [Bind Pattern Exp]
              deriving (Eq, Generic, Show, NominalSupport, NominalShow, Nominal)

-- | patterns bind only term variables
data Pattern = PApp Id [Either (NoBind Exp) Variable] 
             deriving (Eq, Generic, NominalShow, NominalSupport, Nominal, Bindable)


{-
instance Disp Pattern where
  display flag (PApp id vs) =
    display flag id <+>
    hsep (map helper vs) 
    where helper (Left (NoBind x)) =
            braces $ display flag x
          helper (Right (x, NoBind c)) = display flag x 

instance Disp (Either (NoBind Exp) (Variable, NoBind UseFlag)) where
  display flag (Left (NoBind e)) = braces $ display flag e
  display flag (Right (x, _)) = display flag x

-- | Branches for the case expression.

-- | Basic gates, with a list of parameters specified, input, output, generalized controls.
-- Note that the variables in the inputs and outputs denote wires, while
-- the variables in the parameter can only be 'regular parameter type'.

-- | Identity circuit.
morphism_id obj = Morphism obj [] obj

-- | Count the number gates in a circuit expression.
gateCount :: Exp -> Integer
gateCount (Wired (Abst ws m)) =
  case m of
    Morphism _ gs _ -> genericLength gs

-- | Erase all the position information in an expression.
erasePos (Pos _ e) = erasePos e
erasePos (Unit) = Unit
erasePos (Set) = Set
erasePos (Sort) = Sort
erasePos Star = Star
erasePos a@(Var x) = a
erasePos a@(Label x) = a
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
erasePos (AppDep' e1 e2) = AppDep' (erasePos e1) (erasePos e2)
erasePos (AppDict e1 e2) = AppDict (erasePos e1) (erasePos e2)
erasePos (AppImp e1 e2) = AppImp (erasePos e1) (erasePos e2)
erasePos (Tensor e1 e2) = Tensor (erasePos e1) (erasePos e2)
erasePos (Pair e1 e2) = Pair (erasePos e1) (erasePos e2)
erasePos (Pack e1 e2) = Pack (erasePos e1) (erasePos e2)
erasePos (Arrow e1 e2) = Arrow (erasePos e1) (erasePos e2)
erasePos (Arrow' e1 e2) = Arrow' (erasePos e1) (erasePos e2)
erasePos (Imply e1 e2) = Imply (map erasePos e1) (erasePos e2)
erasePos (Bang e) = Bang $ erasePos e
erasePos (UnBox) = UnBox
erasePos (Revert) = Revert
erasePos a@(RealNum) = a
erasePos a@(WrapR _) = a
erasePos a@(RealOp _) = a
erasePos (RunCirc) = RunCirc
erasePos (Box) = Box
erasePos a@(ExBox) = a
erasePos (Lift e) = Lift $ erasePos e
erasePos (Force e) = Force $ erasePos e
erasePos (Force' e) = Force' $ erasePos e
erasePos a@(Wired _) = a 
erasePos (Circ e1 e2) = Circ (erasePos e1) (erasePos e2)
erasePos (Pi (Abst vs b) e) = Pi (abst vs (erasePos b)) (erasePos e)
erasePos (Pi' (Abst vs b) e) = Pi' (abst vs (erasePos b)) (erasePos e)
erasePos (PiImp (Abst vs b) e) = PiImp (abst vs (erasePos b)) (erasePos e)
erasePos (Exists (Abst vs b) e) = Exists (abst vs (erasePos b)) (erasePos e)
erasePos (Forall (Abst vs b) e) = Forall (abst vs (erasePos b)) (erasePos e)
erasePos (Forall' (Abst vs b) e) = Forall' (abst vs (erasePos b)) (erasePos e)
erasePos (Lam (Abst vs b) cs) = Lam (abst vs (erasePos b)) cs
erasePos (Lam' (Abst vs b)) = Lam' (abst vs (erasePos b)) 
erasePos (LamTm (Abst vs b)) = LamTm (abst vs (erasePos b))
erasePos (LamDep (Abst vs b) cs) = LamDep (abst vs (erasePos b)) cs
erasePos (LamImp (Abst vs b)) = LamImp (abst vs (erasePos b)) 
erasePos (LamType (Abst vs b)) = LamType (abst vs (erasePos b))
erasePos (LamDict (Abst vs b)) = LamDict (abst vs (erasePos b))
erasePos (Let m (Abst vs b) c) = Let (erasePos m) (abst vs (erasePos b)) c
erasePos (LetPair m (Abst xs b) cs) = LetPair (erasePos m) (abst xs (erasePos b)) cs
erasePos (LetEx m (Abst (x, y) b) cs) = LetEx (erasePos m) (abst (x, y) (erasePos b)) cs
erasePos (LetPat m (Abst (PApp id vs) b)) = LetPat (erasePos m) (abst (PApp id vs) (erasePos b))
erasePos (Case e (B br)) = Case (erasePos e) (B (map helper br))
  where helper (Abst p m) = abst p (erasePos m)
erasePos e = error $ "from erasePos " ++ (show $ disp e)

-- | Decompose a expression into bodies and head, with variables intact.
-- e.g. unfoldExp ((x :: A1) -> A2 -> (P) => H) produces
-- ([(Just (Right x), A1), (Nothing, A2), (Nothing, P)], H)
unfoldExp :: Exp -> ([(Maybe Variable, Exp)], Exp)
unfoldExp (Pos p a) = unfoldExp a
unfoldExp (Arrow t1 t2) =
  let (res, h) = unfoldExp t2 in
  ((Nothing, t1):res, h)
unfoldExp (Pi (Abst vs t2) t1) = 
  let (res, h) = unfoldExp t2 in
  (map (\ x -> (Just x, t1)) vs ++ res, h)
unfoldExp (Imply t1 t2) =
  let (res, h) = unfoldExp t2 in
  ((map (\ x -> (Nothing, x)) t1)++ res, h)  
unfoldExp a = ([], a)  

-- | Similar to unfoldExp, it decompose a type into bodies and head.
-- But the bind variables are discarded. 
-- e.g. deCompose ((x :: A1) -> A2 -> H) gives ([A1, A2], H)
deCompose :: Exp -> ([Exp], Exp)
deCompose (Pos p a) = deCompose a
deCompose (Arrow t1 t2) =
  let (res, h) = deCompose t2 in
  (t1:res, h)
deCompose (Imply t1 t2) =
  let (res, h) = deCompose t2 in
  (t1 ++ res, h)  
deCompose (Pi (Abst vs t2') t1) = 
  let (res, h) = deCompose t2' in
  (map (\ x -> t1) vs ++ res, h)  
deCompose a = ([], a)  


-- | 'getId' obtains the head constructor of an expression, it can
-- be applied to both type and term expression. It return Nothing if the input is not
-- in a applicative form. Left indicates the identifier is a term constructor, Right 
-- indicates the identifier is a type construtor.
-- getId also returns a list of computational relevant arguments, note that the arguments
-- for AppType and AppTm are not considered relevant.
--   . 
getId :: Exp -> Maybe (Either Id Id, [Exp])
getId (Base id) = return (Right id, [])
getId (LBase id) = return (Right id, [])
getId (Const id) = return (Left id, [])
getId (App t1 t2) =
  do (id, args) <- getId t1
     return (id, args ++ [t2])
getId (App' t1 t2) =
  do (id, args) <- getId t1
     return (id, args ++ [t2])     
getId (AppDep t1 t2) =
  do (id, args) <- getId t1
     return (id, args ++ [t2])
-- getId (AppImp t1 t2) =
--   do (id, args) <- getId t1
--      return (id, args ++ [t2])     
getId (AppDict t1 t2) =
  do (id, args) <- getId t1
     return (id, args ++ [t2])          
getId (AppType t1 t2) = getId t1
getId (AppTm t1 t2) = getId t1
  -- do (id, args) <- getId t1
  --    return (id, args ++ [t2])
getId (Pos p e) = getId e
getId _ = Nothing

-- | unwind an applicative expression into its spine form
unwind (App t1 t2) =
  let (h, args) = unwind t1
  in (h, args++[t2])
unwind (Pos p e) = unwind e
unwind a = (a, [])

-- | Similar to ''unwind'', except according to ''AppTm'' 
unwindTm (AppTm t1 t2) =
  let (h, args) = unwindTm t1
  in (h, args++[t2])
unwindTm (Pos p e) = unwindTm e
unwindTm a = (a, [])

-- | Similar to ''unwind'', except according to ''AppType'' 
unwindType (AppType t1 t2) =
  let (h, args) = unwindType t1
  in (h, args++[t2])
unwindType (Pos p e) = unwindType e
unwindType a = (a, [])

-- | Similar to ''unwind'', except according to ''AppDep'' 
unwindDep (AppDep t1 t2) =
  let (h, args) = unwindDep t1
  in (h, args++[t2])
unwindDep (Pos p e) = unwindDep e
unwindDep a = (a, [])


-- | Flatten a n-tuple into a list. 
unPair n (Pos _ e) = unPair n e
unPair n (Pair x y) | n == 2 = Just [x, y]
unPair n (Pair x y) | n > 2 =
  do r <- unPair (n-1) x
     return (r++[y])
unPair _ _ = Nothing

-- | Flatten a multi-tensor into a list. 
unTensor n (Pos _ e) = unTensor n e
unTensor n (Tensor x y) | n == 2 = Just [x, y]
unTensor n (Tensor x y) | n > 2 =
  do r <- unTensor (n-1) x
     return (r++[y])
unTensor _ _ = Nothing


-- | A predicate to tell whether an expression is a variable. 
isVar (Var _) = True
isVar (Pos p e) = isVar e
isVar _ = False

-- | A predicate to tell whether an expression is a eigenvariable. 
isEigenVar (EigenVar _) = True
isEigenVar (Pos p e) = isEigenVar e
isEigenVar _ = False

-- | A predicate to tell whether an expression is a constant. 
isConst (Const _) = True
isConst (Pos p e) = isConst e
isConst _ = False

-- | A predicate to tell whether an expression consists of only simple arrows.
-- i.e., the base should be not of application form. 
isArrow (Pos p e) = isArrow e
isArrow (Arrow a b) = isArrow a && isArrow b
isArrow (LBase _) = True
isArrow (Base _) = True
isArrow (Set) = True
isArrow (Unit) = True
isArrow a = False

-- | Determine whether an expression is a kind expression. Note we allow
-- dependent kind such as: (a :: Type) -> (x :: !a) -> Type. 
isKind (Set) = True
isKind (Arrow k1 k2) = isKind k2
isKind (Arrow' k1 k2) = isKind k2
isKind (Pi b ty) = open b $ \ vs b' -> isKind b'
isKind (Pi' b ty) = open b $ \ vs b' -> isKind b'
-- isKind (PiImp b ty) = open b $ \ vs b' -> isKind b'
isKind (Forall b ty) = open b $ \ vs b' -> isKind b'
isKind (Forall' b ty) = open b $ \ vs b' -> isKind b'
isKind (Pos _ e) = isKind e
isKind _ = False

-- | Convert an implicit type to its explicit version
toExplicit (Forall (Abst [] t) ty) = toExplicit t
toExplicit (Forall (Abst (x:xs) t) ty) =
  Forall (abst [x] $ toExplicit (Forall (abst xs t) ty)) ty

toExplicit (Pi (Abst [] t) ty) = toExplicit t
toExplicit (Pi (Abst (x:xs) t) ty) =
  Pi (abst [x] $ toExplicit (Pi (abst xs t) ty)) ty

toExplicit (PiImp (Abst [] t) ty) = toExplicit t
toExplicit (PiImp (Abst (x:xs) t) ty) =
  Pi (abst [x] $ toExplicit (PiImp (abst xs t) ty)) ty
toExplicit (Imply bd ty) =
  Imply bd $ toExplicit ty
toExplicit (Arrow ty1 ty2) =
  Arrow (toExplicit ty1) (toExplicit ty2)
toExplicit (Pos _ a) = toExplicit a
toExplicit (Bang a) = Bang $ toExplicit a
toExplicit a = a


-- | Removing all the bang/forall prefixes of a type expression.
removePrefix (Bang a) = removePrefix a
removePrefix (Forall bd ty) =
  open bd $ \ vs m -> removePrefix m
removePrefix (Pos _ a) = removePrefix a                      
removePrefix a = a

-- | Decompose and return the leading forall quantifiers. It makes a
-- distinction on on Forall variables and PiImp variables.
decomposeForall' :: Exp -> ([Either (Variable, Exp) (Variable, Exp)], Exp)
decomposeForall' (Forall bd ty) =
  open bd $ \ vs m ->
  let vs' = map (\ x -> Right (x, ty)) vs
      (xs, m') = decomposeForall' m
  in (vs' ++ xs, m')
decomposeForall' (PiImp bd ty) =
  open bd $ \ vs m ->
  let vs' = map (\ x -> Left (x, ty)) vs
      (xs, m') = decomposeForall' m
  in (vs' ++ xs, m')     
decomposeForall' (Pos _ a) = decomposeForall' a
decomposeForall' a = ([], a)

-- | Decompose and return the leading forall quantifiers.
decomposeForall :: Exp -> ([(Variable, Exp)], Exp)
decomposeForall e = let (r, e') = decomposeForall' e
                        r' = map (\ x -> case x of
                                     Left p -> p
                                     Right p -> p
                                 ) r
                    in (r', e')

-- | Decompose and return the leading forall and class quantifiers.
decomposePrefixes :: Exp -> ([(Maybe (Either Variable Variable), Exp)], Exp)
decomposePrefixes (Forall bd ty) =
  open bd $ \ vs m ->
  let vs' = map (\ x -> (Just (Right x), ty)) vs
      (xs, m') = decomposePrefixes m
  in (vs' ++ xs, m')
decomposePrefixes (PiImp bd ty) =
  open bd $ \ vs m ->
  let vs' = map (\ x -> (Just (Left x), ty)) vs
      (xs, m') = decomposePrefixes m
  in (vs' ++ xs, m')     
decomposePrefixes (Imply bd ty) =
  let vs' = map (\ x -> (Nothing, x)) bd
      (xs, m') = decomposePrefixes ty
  in (vs' ++ xs, m')
decomposePrefixes (Pos _ a) = decomposePrefixes a
decomposePrefixes a = ([], a)

-- | A flag for getting free variables in an expression.
data VarSwitch = GetGoal -- ^ Get goal variables only.
  | AllowEigen  -- ^ Free variables in clude eigen variables
  | NoEigen -- ^ Free variables does not clude eigen variables
  | NoImply -- ^ Does not include the variables that occurs in the type class constraints. 
  | OnlyEigen  -- ^ Obtain only eigen variables from an expression.
  | All
-- | Obtain the set of variables in an expression.
free_vars :: VarSwitch -> Exp -> S.Set Variable
free_vars AllowEigen (EigenVar x) = S.insert x S.empty
free_vars OnlyEigen (EigenVar x) = S.insert x S.empty
free_vars All (EigenVar x) = S.insert x S.empty
free_vars All (Label x) = S.insert x S.empty
free_vars a (Label x) = S.empty
free_vars NoEigen (EigenVar _) = S.empty
free_vars GetGoal (EigenVar _) = S.empty
free_vars NoImply (EigenVar x) = S.insert x S.empty
free_vars GetGoal (Var x) = S.empty
free_vars OnlyEigen (Var x) = S.empty
free_vars b (Var x) = S.insert x S.empty
free_vars OnlyEigen (GoalVar x) = S.empty
free_vars GetGoal (GoalVar x) = S.insert x S.empty
free_vars All (GoalVar x) = S.insert x S.empty
free_vars b (GoalVar x) = S.empty
free_vars b (Base _) = S.empty
free_vars b (LBase _) = S.empty
free_vars b (Const _) = S.empty
free_vars b (Unit) = S.empty
free_vars b (Star) = S.empty
free_vars b (Set) = S.empty
free_vars b (UnBox) = S.empty
free_vars b (Revert) = S.empty
free_vars b (RealNum) = S.empty
free_vars b (WrapR _) = S.empty
free_vars b (RealOp _) = S.empty
free_vars b (RunCirc) = S.empty
free_vars b (App t t') =
  free_vars b t `S.union` free_vars b t'
free_vars b (App' t t') =
  free_vars b t `S.union` free_vars b t'  
free_vars b (AppType t t') =
  free_vars b t `S.union` free_vars b t'
free_vars b (AppDep t t') =
  free_vars b t `S.union` free_vars b t'
free_vars b (AppDep' t t') =
  free_vars b t `S.union` free_vars b t'  
free_vars b (AppDict t t') =
  free_vars b t `S.union` free_vars b t'    
free_vars b (AppTm t t') =
  free_vars b t `S.union` free_vars b t'
free_vars b (AppImp t t') =
  free_vars b t `S.union` free_vars b t'
  
free_vars b (Tensor ty tm) =
  free_vars b ty `S.union` free_vars b tm
free_vars b (Arrow ty tm) =
  free_vars b ty `S.union` free_vars b tm
free_vars b (Arrow' ty tm) =
  free_vars b ty `S.union` free_vars b tm  
free_vars NoImply (Imply ty tm) = free_vars NoImply tm
free_vars b (Imply ty tm) =
  (S.unions $ map (free_vars b) ty) `S.union` free_vars b tm  
free_vars b (Bang t) = free_vars b t
free_vars b (Pi bind t) =
  free_vars b t `S.union`
  (open bind $ \ xs m -> free_vars b m `S.difference` S.fromList xs)
free_vars b (Pi' bind t) =
  free_vars b t `S.union`
  (open bind $ \ xs m -> free_vars b m `S.difference` S.fromList xs)  
free_vars b (PiImp bind t) =
  free_vars b t `S.union`
  (open bind $ \ xs m -> free_vars b m `S.difference` S.fromList xs)  
free_vars b (Exists bind t) =
  free_vars b t `S.union`
  (open bind $ \ xs m -> free_vars b m `S.difference` S.fromList [xs])
free_vars b (Lam bind _) =
  open bind $ \ xs m -> free_vars b m `S.difference` S.fromList xs
free_vars b (Lam' bind) =
  open bind $ \ xs m -> free_vars b m `S.difference` S.fromList xs  
free_vars b (LamImp bind) =
  open bind $ \ xs m -> free_vars b m `S.difference` S.fromList xs                        
free_vars b (LamType bind) =
  open bind $ \ xs m -> free_vars b m `S.difference` S.fromList xs
free_vars b (LamDep bind _) =
  open bind $ \ xs m -> free_vars b m `S.difference` S.fromList xs
free_vars b (LamDep' bind) =
  open bind $ \ xs m -> free_vars b m `S.difference` S.fromList xs                          
free_vars b (LamTm bind) =
  open bind $ \ xs m -> free_vars b m `S.difference` S.fromList xs
free_vars b (LamDict bind) =
  open bind $ \ xs m -> free_vars b m `S.difference` S.fromList xs                        
free_vars b (LamAnn ty bind _) =
    free_vars b ty `S.union` (open bind $ \ xs m -> free_vars b m `S.difference` S.fromList [xs])
                        
free_vars b (Forall bind ty) =
  open bind $ \ xs m -> S.union (free_vars b m `S.difference` S.fromList xs) (free_vars b ty)
free_vars b (Forall' bind ty) =
  open bind $ \ xs m -> S.union (free_vars b m `S.difference` S.fromList xs) (free_vars b ty)                        
free_vars b (Circ t u) = S.union (free_vars b t) (free_vars b u)
free_vars b (Pair ty tm) =
  free_vars b ty `S.union` free_vars b tm
free_vars b (Pack ty tm) =
  free_vars b ty `S.union` free_vars b tm
free_vars b (WithType ty tm) =
  free_vars b ty `S.union` free_vars b tm

free_vars b (Let t bind _) =
  free_vars b t `S.union`
  (open bind $ \ x m -> S.delete x (free_vars b m))

free_vars b (LetAnn bind t m _) =
  free_vars b t `S.union` free_vars b m `S.union` 
  (open bind $ \ x m -> S.delete x (free_vars b m))

free_vars b (LetPair t bind _) =
  free_vars b t `S.union`
  (open bind $ \ xs m -> (S.difference (free_vars b m) (S.fromList xs)))

free_vars b (LetEx t bind _) =
  free_vars b t `S.union`
  (open bind $ \ (x, y) m -> S.delete y (S.delete x (free_vars b m)))

free_vars b (LetPat t (Abst ps m)) =
  let (bvs, fvs) = pvar ps in
  (free_vars b t `S.union` fvs `S.union` free_vars b m)
  `S.difference` bvs
  where pvar (PApp _ []) = (S.empty, S.empty)
        pvar (PApp k ((Right (x, _)):xs)) =
          let (bv, fv) = pvar (PApp k xs) in
          (S.insert x bv, fv)
        pvar (PApp k ((Left (NoBind x)):xs)) =
          let (bv, fv) = pvar (PApp k xs)
              fbv = free_vars b x
          in (bv, S.union fbv fv)


free_vars b (Force t) = free_vars b t
free_vars b (Force' t) = free_vars b t

free_vars b (Box) = S.empty

free_vars b (ExBox) = S.empty


free_vars b (Lift t) = free_vars b t
  
free_vars b (Case t (B brs)) =
  free_vars b t `S.union` S.unions (map helper brs)
  where helper bind = open bind $ \ ps m ->
          let (bvs, fvs) = pvar ps in
          (fvs `S.union` free_vars b m) `S.difference` bvs
        pvar (PApp _ []) = (S.empty, S.empty)
        pvar (PApp k ((Right (x, _)):xs)) =
          let (bv, fv) = pvar (PApp k xs) in
          (S.insert x bv, fv)
        pvar (PApp k ((Left (NoBind x)):xs)) =
          let (bv, fv) = pvar (PApp k xs)
              fbv = free_vars b x
          in (bv, S.union fbv fv)


free_vars b (Pos p e) = free_vars b e
free_vars b (Wired _) = S.empty
free_vars b a = error $ "from free_vars  " ++ render (disp a)

-- * Substitution
   
-- | The substitution, normally it is represented as a list, but
-- here I am hoping for a minor performance gain, so I use map instead. 
type Subst = Map Variable Exp

-- | Display substitution.
instance Disp (Map Variable Exp) where
  display b vs =
    let vs' = Map.toList vs in
    vcat $ map helper vs'
     where helper (x,  t) = display b x <+> text "|->" <+> display b t

-- | Display a list of variable expression pairs. 
instance Disp [(Variable, Exp)] where
  display b vs' =
    vcat $ map helper vs'
     where helper (x,  t) = display b x <+> text "|->" <+> display b t


-- | Merge two subsitutions, the first argument is the list representation of the substitution.
mergeSubL :: [(Variable, Exp)] -> Map Variable Exp -> Map Variable Exp
mergeSubL new old =
  let new' = Map.fromList new in
  new' `Map.union` Map.map (substitute new') old

-- | Merge two subsitutions.
mergeSub :: Map Variable Exp -> Map Variable Exp -> Map Variable Exp
mergeSub new old =
  new `Map.union` Map.map (substitute new) old

-- | A list version of 'substitute'.
apply s t = let s' = Map.fromList s in substitute s' t

-- | Capture avoiding substitution, also substitute eigenvariables
substitute' s a@(Label y) = a

substitute' s a@(Var y) =
  case Map.lookup y s of
    Nothing -> a
    Just t -> t

substitute' s a@(GoalVar y) =
  case Map.lookup y s of
    Nothing -> a
    Just t -> t
    
substitute' s a@(EigenVar y) = 
  case Map.lookup y s of
    Nothing -> a
    Just t -> t

substitute' s a@(Base _) = a

substitute' s a@(LBase _) = a      
substitute' s a@(Unit) = a
substitute' s a@(Set) = a
substitute' s a@(Sort) = a
substitute' s a@(Star) = a
substitute' s a@(Const _) = a
substitute' s (Arrow t t') =
  let t1' = substitute' s t
      t2' = substitute' s t'
  in Arrow t1' t2'
substitute' s (Arrow' t t') =
  let t1' = substitute' s t
      t2' = substitute' s t'
  in Arrow' t1' t2'  
substitute' s (Imply t t') =
  let t1' = map (substitute' s) t
      t2' = substitute' s t'
  in Imply t1' t2'  
substitute' s (Tensor t t') =
  let t1' = substitute' s t
      t2' = substitute' s t'
  in Tensor t1' t2'
substitute' s (Circ t t') =
  let t1' = substitute' s t
      t2' = substitute' s t'
  in Circ t1' t2'
substitute' s (Bang t) = Bang (substitute' s t)

substitute' s (Pi bind t) =
  open bind $
  \ ys m -> Pi (abst ys (substitute' s m))
           (substitute' s t) 

substitute' s (Pi' bind t) =
  open bind $
  \ ys m -> Pi' (abst ys (substitute' s m))
            (substitute' s t) 

substitute' s (PiImp bind t) =
  open bind $
  \ ys m -> PiImp (abst ys (substitute' s m))
           (substitute' s t) 

substitute' s (Exists bind t) =
  open bind $
  \ ys m -> Exists (abst ys (substitute' s m))
           (substitute' s t) 

substitute' s (Forall bind t) =
  open bind $
  \ ys m -> Forall (abst ys (substitute' s m))
           (substitute' s t) 

substitute' s (Forall' bind t) =
  open bind $
  \ ys m -> Forall' (abst ys (substitute' s m))
           (substitute' s t) 

substitute' s (App t tm) =
  App (substitute' s t) (substitute' s tm)

substitute' s (App' t tm) =
  App' (substitute' s t) (substitute' s tm)
  
substitute' s (AppType t tm) =
  AppType (substitute' s t) (substitute' s tm)

substitute' s (AppTm t tm) =
  AppTm (substitute' s t) (substitute' s tm)
substitute' s (AppImp t tm) =
  AppImp (substitute' s t) (substitute' s tm)  
substitute' s (AppDep t tm) =
  AppDep (substitute' s t) (substitute' s tm)
substitute' s (AppDep' t tm) =
  AppDep' (substitute' s t) (substitute' s tm)  
substitute' s (AppDict t tm) =
  AppDict (substitute' s t) (substitute' s tm)

substitute' s (Lam bind cs) =
  open bind $
  \ ys m -> Lam (abst ys (substitute' s m)) cs

substitute' s (Lam' bind) =
  open bind $
  \ ys m -> Lam' (abst ys (substitute' s m)) 

substitute' s (LamAnn ty bind c) =
  open bind $
  \ ys m -> let ty' = substitute' s ty in LamAnn ty' (abst ys (substitute' s m)) c

substitute' s (LamType bind) =
  open bind $
  \ ys m -> LamType (abst ys (substitute' s m)) 

substitute' s (LamTm bind) =
  open bind $
  \ ys m -> LamTm (abst ys (substitute' s m)) 

substitute' s (LamDict bind) =
  open bind $
  \ ys m -> LamDict (abst ys (substitute' s m)) 

substitute' s (LamImp bind) =
  open bind $
  \ ys m -> LamImp (abst ys (substitute' s m)) 

substitute' s (LamDep bind cs) =
  open bind $
  \ ys m -> LamDep (abst ys (substitute' s m)) cs

substitute' s (LamDep' bind) =
  open bind $
  \ ys m -> LamDep' (abst ys (substitute' s m)) 

substitute' s (Pair t tm) =
  Pair (substitute' s t) (substitute' s tm)
substitute' s (Pack t tm) =
  Pack (substitute' s t) (substitute' s tm)
substitute' s (WithType t tm) =
  WithType (substitute' s t) (substitute' s tm)
substitute' s (Force t) = Force (substitute' s t)
substitute' s (Force' t) = Force' (substitute' s t)
substitute' s (Lift t) = Lift (substitute' s t)
substitute' s (UnBox) = UnBox
substitute' s (Revert) = Revert
substitute' s a@(RealNum) = a
substitute' s a@(WrapR _) = a
substitute' s a@(RealOp _) = a
substitute' s (RunCirc) = RunCirc
substitute' s a@(Box) = a
substitute' s a@(ExBox) = a
       
substitute' s (Let m bd c) =
  let m' = substitute' s m in
    open bd $ \ y b -> Let m' (abst y (substitute' s b)) c

substitute' s (LetAnn bd ty m c) =
  let m' = substitute' s m
      ty' = substitute' s ty
  in
    open bd $ \ y b -> LetAnn (abst y (substitute' s b)) ty' m' c

substitute' s (LetPair m bd cs) =
  let m' = substitute' s m in
    open bd $ \ ys b -> LetPair m' (abst ys (substitute' s b)) cs

substitute' s (LetEx m bd cs) =
  let m' = substitute' s m in
    open bd $ \ (y, z) b -> LetEx m' (abst (y, z) (substitute' s b)) cs


substitute' s (LetPat m bd) =
  let m' = substitute' s m in
   open bd $ \ ps b ->  LetPat m' (abst ps (substitute' s b))

substitute' s (Case tm (B br)) =
  Case (substitute' s tm) (B (helper' br))
  where helper' ps =
          map (\ b -> open b $
                       \ ys m ->
                       abst ys (substitute' s m))
          ps

substitute' s (Pos p e) = Pos p (substitute' s e)
substitute' s a@(Wired _) = a
substitute' s a = error ("from substitute': " ++ show (disp a))  

-- | The substitution will substitute eigenvar to eigenterms
substitute s a =
  let vs = free_vars OnlyEigen a
      s' = Map.mapWithKey (\ k v -> if k `S.member` vs then toEigen v else v) s
  in substitute' s' a
  where toEigen v =
          let fvs = S.toList $ free_vars AllowEigen v
              subs = Map.fromList $ map (\ y -> (y, EigenVar y)) fvs
          in substitute' subs v
          

-- | check if a variable is used as implicit variable in an annotated term
isImplicit s (App t tm) =
   (isImplicit s t) || (isImplicit s tm)
isImplicit s (AppType t tm) =
  (isImplicit s t)
isImplicit s (AppTm t tm) =
   (isImplicit s t) || (isImplicit s tm)
isImplicit s (AppImp t tm) =
  let vars = free_vars AllowEigen tm
  in if s `S.member` vars then True
     else isImplicit s t

isImplicit s (AppDep t tm) =
   (isImplicit s t) || (isImplicit s tm)

isImplicit s (AppDict t tm) =
   (isImplicit s t) 

isImplicit s (Pi bind _) =
  open bind $
  \ ys m -> (isImplicit s m)

isImplicit s (PiImp bind _) =
  open bind $
  \ ys m -> (isImplicit s m)

isImplicit s (Forall bind _) =
  open bind $
  \ ys m -> (isImplicit s m)

isImplicit s (Lam bind _) =
  open bind $
  \ ys m -> isImplicit s m

isImplicit s (LamAnn ty bind _) =
  open bind $
  \ ys m -> (isImplicit s m)

isImplicit s (LamType bind) =
  open bind $
  \ ys m -> isImplicit s m 

isImplicit s (LamTm bind) =
  open bind $
  \ ys m -> isImplicit s m

isImplicit s (LamImp bind) =
  open bind $
  \ ys m -> isImplicit s m

isImplicit s (LamDep bind _) =
  open bind $
  \ ys m -> isImplicit s m

isImplicit s (Pair t tm) =
   (isImplicit s t) || (isImplicit s tm)
isImplicit s (Pack t tm) =
   (isImplicit s t) || (isImplicit s tm)
isImplicit s (WithType t tm) =
  (isImplicit s tm)

isImplicit s (Force t) = (isImplicit s t)
isImplicit s (Force' t) = (isImplicit s t)
isImplicit s (Lift t) = (isImplicit s t)
       
isImplicit s (Let m bd _) =
  if isImplicit s m then True
  else open bd $ \ y b -> isImplicit s b

isImplicit s (LetAnn bd ty m _) =
  if isImplicit s m then True
  else 
    open bd $ \ y b -> isImplicit s b

isImplicit s (LetPair m bd _) =
  if isImplicit s m then True
  else 
    open bd $ \ ys b -> isImplicit s b

isImplicit s (LetEx m bd _) =
  if isImplicit s m then True
  else open bd $ \ (y, z) b -> isImplicit s b


isImplicit s (LetPat m bd) =
  if isImplicit s m then True
  else open bd $ \ ps b ->  isImplicit s b

isImplicit s (Case tm (B br)) =
  if isImplicit s tm then True
  else or (helper' br)
  where helper' ps =
          map (\ b -> open b $
                       \ ys m ->
                        (isImplicit s m))
          ps
isImplicit s (Arrow t tm) =
   (isImplicit s t) || (isImplicit s tm)
   
isImplicit s (Pos p e) = isImplicit s e
isImplicit s a = False

-- | check if a variable is used as explicit variable (i.e. retained for runtime)
-- in an annotated term

-- isExplicit s a | trace (show $ disp a) False  = undefined
isExplicit s (App t tm) =
   (isExplicit s t) || (isExplicit s tm)
isExplicit s (AppType t tm) =
  (isExplicit s t)
isExplicit s (AppTm t tm) =
   (isExplicit s t)
isExplicit s (AppImp t tm) =
  (isExplicit s t) || (isExplicit s tm)

isExplicit s (AppDep t tm) =
   (isExplicit s t) || (isExplicit s tm)
isExplicit s (AppDict t tm) =
   (isExplicit s t) 

isExplicit s (Lam bind _) =
  open bind $
  \ ys m -> isExplicit s m

isExplicit s (LamAnn ty bind _) =
  open bind $
  \ ys m -> (isExplicit s m)

isExplicit s (LamType bind) =
  open bind $
  \ ys m -> isExplicit s m 

isExplicit s (LamTm bind) =
  open bind $
  \ ys m -> isExplicit s m

isExplicit s (LamImp bind) =
  open bind $
  \ ys m -> isExplicit s m

isExplicit s (LamDep bind _) =
  open bind $
  \ ys m -> isExplicit s m

isExplicit s (Pair t tm) =
   (isExplicit s t) || (isExplicit s tm)
isExplicit s (Pack t tm) =
   (isExplicit s t) || (isExplicit s tm)
isExplicit s (WithType t tm) =
  (isExplicit s tm)

isExplicit s (Force t) = (isExplicit s t)
isExplicit s (Force' t) = (isExplicit s t)
isExplicit s (Lift t) = (isExplicit s t)
       
isExplicit s (Let m bd _) =
  if isExplicit s m then True
  else open bd $ \ y b -> isExplicit s b

isExplicit s (LetAnn bd ty m _) =
  if isExplicit s m then True
  else 
    open bd $ \ y b -> isExplicit s b

isExplicit s (LetPair m bd _) =
  if isExplicit s m then True
  else 
    open bd $ \ ys b -> isExplicit s b

isExplicit s (LetEx m bd _) =
  if isExplicit s m then True
  else open bd $ \ (y, z) b -> isExplicit s b


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
isExplicit s a = False


-- | Replace the bounded eigen variable to variable.
unEigen = unEigenBound []

-- | Helper function for unEigen
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
  
unEigenBound vars (AppType e1 e2) =
  let e1' = (unEigenBound vars e1)
      e2' = (unEigenBound vars e2)
  in AppType e1' e2'  

unEigenBound vars (AppTm e1 e2) =
  let e1' = (unEigenBound vars e1)
      e2' = (unEigenBound vars e2)
  in AppTm e1' e2'  

unEigenBound vars (AppImp e1 e2) =
  let e1' = (unEigenBound vars e1)
      e2' = (unEigenBound vars e2)
  in AppImp e1' e2'  

unEigenBound vars (AppDep e1 e2) =
  let e1' = (unEigenBound vars e1)
      e2' = (unEigenBound vars e2)
  in AppDep e1' e2'  

unEigenBound vars (AppDep' e1 e2) =
  let e1' = (unEigenBound vars e1)
      e2' = (unEigenBound vars e2)
  in AppDep' e1' e2'  

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

unEigenBound vars (WithType e1 e2) = 
  let e1' = (unEigenBound vars e1)
      e2' = (unEigenBound vars e2)
  in WithType e1' e2'

unEigenBound vars (Pack e1 e2) = 
  let e1' = (unEigenBound vars e1)
      e2' = (unEigenBound vars e2)
  in Pack e1' e2' 

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
unEigenBound vars a@(RealNum) = a
unEigenBound vars a@(WrapR _) = a
unEigenBound vars a@(RealOp _) = a
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

unEigenBound vars (LetPair m bd cs) = open bd $ \ xs b ->
  let m' = (unEigenBound vars m)
      b' = (unEigenBound (xs ++ vars) b)
  in LetPair m' (abst xs b') cs

unEigenBound vars (LetEx m bd cs) = open bd $ \ (x, y) b ->
  let m' = (unEigenBound vars m)
      b' = (unEigenBound (x:y:vars) b)
  in LetEx m' (abst (x, y) b') cs

unEigenBound vars (LetPat m bd) = open bd $ \ (PApp id vs) b ->
  let m' = unEigenBound vars m
      (bvs, vs') = pvar vs
      b' = unEigenBound (bvs ++ vars) b
  in LetPat m' (abst (PApp id vs') b')
 where  pvar ([]) = ([], [])
        pvar (Right x : xs) =
          let (bv, fv) = pvar xs in
          (fst x:bv, Right x : fv)
        pvar (Left (NoBind (Var x)):xs) =
          let (bv, fv) = pvar xs in
          if x `elem` vars then
            (bv, Left (NoBind (Var x)):fv)
          else (x:bv, Right (x, NoBind NonLinear) : fv)
        pvar (Left (NoBind (EigenVar x)):xs) =
          let (bv, fv) = pvar xs in
          if x `elem` vars then
            (bv, Left (NoBind (Var x)):fv)
          else (x:bv, Right (x, NoBind NonLinear) :fv)
          
        pvar ((Left (NoBind x)):xs) =
          let (bv, fv) = pvar xs
              x' = unEigenBound vars x
          in (bv, Left (NoBind x'):fv)
   
unEigenBound vars (Let m bd c) = open bd $ \ p b ->
  let m' = (unEigenBound vars m)
      b' = (unEigenBound (p:vars) b)
  in Let m' (abst p b') c

unEigenBound vars (LetAnn bd ty m c) = open bd $ \ p b ->
  let m' = (unEigenBound vars m)
      b' = (unEigenBound (p:vars) b)
      ty' = unEigenBound vars ty
  in LetAnn (abst p b') ty' m' c

unEigenBound vars (LamAnn ty bd c) =
  open bd $ \ xs m ->
   let m' = unEigenBound (xs:vars) m
       ty' = unEigenBound vars ty
   in LamAnn ty' (abst xs m') c

unEigenBound vars (LamTm bd) =
  open bd $ \ xs m ->
   let m' = unEigenBound (xs ++ vars) m
   in LamTm $ abst xs m'

unEigenBound vars (LamImp bd) =
  open bd $ \ xs m ->
   let m' = unEigenBound (xs ++ vars) m
   in LamImp (abst xs m')

unEigenBound vars (LamDep bd cs) =
  open bd $ \ xs m ->
   let m' = unEigenBound (xs ++ vars) m
   in LamDep (abst xs m') cs

unEigenBound vars (LamDep' bd) =
  open bd $ \ xs m ->
   let m' = unEigenBound (xs ++ vars) m
   in LamDep' (abst xs m') 

unEigenBound vars (Lam bd cs) =
  open bd $ \ xs m ->
   let m' = unEigenBound (xs ++ vars) m
   in Lam (abst xs m') cs

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

unEigenBound vars (Forall' bd ty) =
  open bd $ \ xs m ->
   let m' = unEigenBound (xs ++ vars) m
       ty' = unEigenBound vars ty
   in Forall' (abst xs m') ty'

unEigenBound vars (PiImp bd ty) =
  open bd $ \ xs m ->
   let m' = unEigenBound (xs ++ vars) m
       ty' = unEigenBound vars ty
   in PiImp (abst xs m') ty'
      
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
          (fst x:bv, (Right x):fv)
        pvar ((Left (NoBind (Var x))):xs) =
          let (bv, fv) = pvar xs in
          if x `elem` vars then
            (bv, (Left (NoBind (Var x))):fv)
          else (x:bv, (Right (x, NoBind NonLinear)):fv)
        pvar ((Left (NoBind (EigenVar x))):xs) =
          let (bv, fv) = pvar xs in
          if x `elem` vars then
            (bv, (Left (NoBind (Var x))):fv)
          else (x:bv, (Right (x, NoBind NonLinear)):fv)
        pvar ((Left (NoBind x)):xs) =
          let (bv, fv) = pvar xs
              x' = unEigenBound vars x
          in (bv, (Left (NoBind x')):fv)
unEigenBound vars a@(Wired _) = a 
unEigenBound vars a = error $ "from unEigenBound" ++ (show $ disp a)



-- | Removing all the vacuous pi quantifiers.
removeVacuousPi :: Exp -> Exp
removeVacuousPi (Pos p e) = Pos p $ removeVacuousPi e
removeVacuousPi (Forall (Abst xs m) ty) =
  Forall (abst xs $ removeVacuousPi m) (removeVacuousPi ty)
removeVacuousPi (PiImp (Abst xs m) ty) =
  PiImp (abst xs $ removeVacuousPi m) (removeVacuousPi ty)  
removeVacuousPi (Pi (Abst xs m) ty) =
  let fvs = free_vars AllowEigen m
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
  
-- | Detect vacuous forall quantifications, returns a list of vacuous variables, their type
--  and the expression that they should occur in. 
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

vacuousForall (Imply ts t2) = vacuousForall t2
vacuousForall (Bang t2) = vacuousForall t2

             
vacuousForall (Forall bds ty) =
  open bds $ \ vs m ->
   let fvs = free_vars NoImply m
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

-- | Convert applicative natural number into a built-in number.  
toInt (App (Const id) t') =
  if getIdName id == "S" then
    do n <- toInt t'
       return $ 1+ n
  else Nothing
toInt (Const id) = 
  if getIdName id == "Z" then
    return 0
  else Nothing
toInt (Pos _ e) = toInt e
toInt _ = Nothing


-- | Obtain the wire names from a simple data value.
getWires (Label x) = [x]
getWires (Const _) = []
getWires Star = []
getWires (App e1 e2) = getWires e1 ++ getWires e2
getWires (AppDep e1 e2) = getWires e1 -- ++ getWires e2
getWires (Pair e1 e2) = getWires e1 ++ getWires e2
getWires a = error $ "applying getWires function to an ill-formed template:" ++ (show $ disp a)


instance Disp Morphism where
  display b (Morphism ins gs outs) =
    (braces $ display b ins) $$
    nest 2 (vcat $ map (display b) gs) $$
    (braces $ display b outs) 

instance Disp Gate where
  display flag (Gate g params ins outs ctrls) =
    disp g <+> brackets (hsep $ punctuate comma (map (display flag) params))
    <+> (braces $ (display flag ins)) <+> (braces $ (display flag outs)) <+> (brackets $ (display flag ctrls))


instance Disp Exp where
  display flag (Var x) = display flag x
  display flag (Label x) = display flag x
  display flag (WrapR (MR len x)) = text $ showCReal (fromInteger len) x
  display flag RealNum = text "Real"
  display flag (RealOp x) = text x
  display flag (GoalVar x) = braces $ display flag x
  display flag (EigenVar x) = brackets (display flag x)
  display flag (Const id) | getIdName id == "Z" = int 0
  display flag (Const id) = display flag id
  display flag (LBase id) = display flag id
  display flag (Base id) = display flag id
  display flag (Pos _ e) = display flag e
  display flag (Lam bds cs) =
    open bds $ \ vs b ->
    fsep [text "\\" , (hsep $ map (display flag) vs), text ".", nest 2 $ display flag b]
  display flag (Lam' bds) =
    open bds $ \ vs b ->
    fsep [text "\\'" , (hsep $ map (display flag) vs), text ".", nest 2 $ display flag b]
  display flag (LamDict bds) =
    open bds $ \ vs b ->
    fsep [text "\\dict" , (hsep $ map (display flag) vs), text ".", nest 2 $ display flag b]    
  display flag (LamAnn ty bds _) =
    open bds $ \ x b ->
    fsep [text "\\" <+> display flag x <+> text "::" <+> display flag ty <+> text ".", nest 2 $ display flag b]
    
  display flag (LamTm bds) =
    open bds $ \ vs b ->
    fsep [text "\\" , (hsep $ map (display flag) vs) <+> text ".", nest 2 $ display flag b]
    
  display flag (LamDep bds _) =
    open bds $ \ vs b ->
    fsep [text "\\" , (hsep $ map (display flag) vs) <+> text ".", nest 2 $ display flag b]
  display flag (LamDep' bds) =
    open bds $ \ vs b ->
    fsep [text "\\'" , (hsep $ map (display flag) vs) <+> text ".", nest 2 $ display flag b]
    
  display flag (LamImp bds) =
    open bds $ \ vs b ->
    fsep [text "\\" , (hsep $ map (\ x -> braces (display flag x) ) vs) <+> text ".", nest 2 $ display flag b]    
    
  display flag (LamType bds) =
    open bds $ \ vs b ->
    fsep [text "\\" , (hsep $ map (display flag) vs) <+> text ".", nest 2 $ display flag b]
  display flag (Forall bds t) =
    open bds $ \ vs b ->
    fsep [text "forall", parens ((hsep $ map (display flag) vs) <+> text "::" <+> display flag t) <+> text ".",
            nest 5 $ display flag b]

  display flag (Forall' bds t) =
    open bds $ \ vs b ->
    fsep [text "forall'", parens ((hsep $ map (display flag) vs) <+> text "::" <+> display flag t) <+> text ".",
            nest 5 $ display flag b]
    
  display flag a@(App t t') =
    case toInt a of
      Nothing -> -- fsep [dParen flag (precedence a - 1) t, dParen flag (precedence a) t']
        case toVec a of
          Nothing ->
            fsep [dParen flag (precedence a - 1) t, dParen flag (precedence a) t']
          Just vs -> brackets $ fsep $ punctuate comma $ map (\ x -> display flag x ) vs
      Just i -> int i
    where
          toVec (Const id) =
            if getIdName id == "VNil" then return []
            else Nothing
          toVec (App (App (Const id) e) res) =
            if getIdName id == "VCons" then
              do vs <- toVec res
                 return $ e:vs
            else Nothing
          toVec _ = Nothing
            
            

  display flag a@(AppType t t') =
     fsep [dParen flag (precedence a - 1) t, dParen flag (precedence a) t']
--    fsep [dParen flag (precedence a - 1) t, text "@3", dParen flag (precedence a) t']
  display flag a@(App' t t') =
     fsep [dParen flag (precedence a - 1) t, dParen flag (precedence a) t']
--    fsep [dParen flag (precedence a - 1) t, text "@2", dParen flag (precedence a) t']
  display flag a@(AppDep t t') =
       fsep [dParen flag (precedence a - 1) t, dParen flag (precedence a) t']
--    fsep [text "@0", dParen flag (precedence a - 1) t, dParen flag (precedence a) t']
  display flag a@(AppDep' t t') =
        fsep [dParen flag (precedence a - 1) t, dParen flag (precedence a) t']
--    fsep [text "@1", dParen flag (precedence a - 1) t, dParen flag (precedence a) t']
    
  display flag a@(AppDict t t') =
    fsep [dParen flag (precedence a - 1) t, dParen flag (precedence a) t']
--    fsep [text "@4", dParen flag (precedence a - 1) t, dParen flag (precedence a) t']
    
  display flag a@(AppTm t t') =
     fsep [dParen flag (precedence a - 1) t, dParen flag (precedence a) t']
--    fsep [text "@5", dParen flag (precedence a - 1) t, dParen flag (precedence a) t']
  display flag a@(AppImp t t') =
    fsep [dParen flag (precedence a - 1) t, braces $ display flag t']    
    
  display flag a@(Bang t) = text "!" <> dParen flag (precedence a - 1) t
  display flag a@(Arrow t1 t2) =
    fsep [dParen flag (precedence a) t1, text "->" , dParen flag (precedence a - 1) t2]
  display flag a@(Arrow' t1 t2) =
    fsep [dParen flag (precedence a) t1, text "->'" , dParen flag (precedence a - 1) t2]    
  display flag (Imply [] t2) = display flag t2
  display flag a@(Imply t1 t2) =
    fsep [parens (fsep $ punctuate comma $ map (display flag) t1), text "=>" , nest 2 $ display flag t2]
    
  display flag Set = text "Type"
  display flag Sort = text "Sort"
  display flag Unit = text "Unit"
  display flag Star = text "()"
  display flag a@(Tensor t t') =
    fsep [dParen flag (precedence a - 1) t,  text "*", dParen flag (precedence a) t']
  display flag (Pair a b) =
    parens $ fsep [display flag a, text "," , display flag b]
  display flag (Pack a b) =
    braces $ display flag a <+> text "," <+> display flag b
    
  display flag (Force m) = text "&" <> display flag m
  display flag (Force' m) = text "&'" <> display flag m
  display flag (Lift m) = text "lift" <+> display flag m

  display flag (Circ u t) =
    text "Circ" <> (parens $ fsep [display flag u <> comma, display flag t])
  display flag (Pi bd t) =
    open bd $ \ vs b ->
    fsep [parens ((hsep $ map (display flag) vs) <+> text "::" <+> display flag t)
    <+> text "->" , nest 2 $ display flag b]
  display flag (Pi' bd t) =
    open bd $ \ vs b ->
    fsep [parens ((hsep $ map (display flag) vs) <+> text "::" <+> display flag t)
    <+> text "->'" , nest 2 $ display flag b]
    
  display flag (PiImp bd t) =
    open bd $ \ vs b ->
    fsep [text "PiImp", braces ((hsep $ map (display flag) vs) <+> text "::" <+> display flag t)
    <+> text "." , nest 2 $ display flag b]
    
  display flag (Exists bd t) =
    open bd $ \ v b ->
    fsep [text "exists" <+> display flag v <+> text "::" <+> display flag t,
           text "." , nest 2 $ display flag b]    
  display flag (Box) = text "box"
  display flag (ExBox) = text "existsBox"
  display flag (UnBox) = text "unbox" 
  display flag (Revert) = text "revert"
  display flag (RunCirc) = text "runCirc"
  display flag (Let m bd _) =
    open bd $ \ x b ->
    fsep [text "let" <+> display flag x <+> text "=", display flag m,
          text "in" <+> display flag b]
  display flag (LetAnn bd ty m _) =
    open bd $ \ x b ->
    fsep [text "let" <+> display flag x <+> text "::" <+> display flag ty $$
          nest 3 (display flag x <+> text "=" <+> display flag m),
          text "in" <+> display flag b]
    
  display flag (LetPair m bd cs) =
    open bd $ \ xs b ->
    fsep [text "let" <+> parens (hsep $ punctuate comma $ map (display flag) xs), text "=", display flag m ,
           text "in" <+> display flag b]
  display flag (LetEx m bd _) =
    open bd $ \ (x, y) b ->
    fsep [text "let" <+> braces (display flag x<>comma<+> display flag y) <+> text "=", display flag m ,
           text "in" <+> display flag b]
    
  display flag (LetPat m bd) =
    open bd $ \ ps b ->
    fsep [text "let" <+> (display flag ps) <+> text "=" , display flag m,
          text "in" <+> display flag b]
  display flag (Case e (B brs)) =
    text "case" <+> display flag e <+> text "of" $$
    nest 2 (vcat $ map helper brs)
    where helper bd =
            open bd $ \ p b -> fsep [display flag p, text "->" , nest 2 (display flag b)]

  display flag (WithType m t) =
    fsep [text "withType" <+> display flag t <+> text ":", display flag m]

  display flag (Wired bd) = 
   open bd $ \ wires e -> (display flag e)
  display flag e = error $ "from display: " ++ show e
  precedence (Var _ ) = 12
  precedence (GoalVar _ ) = 12
  precedence (EigenVar _ ) = 12
  precedence (RealNum) = 12
  precedence (RealOp _) = 12
  precedence (WrapR _) = 12
  precedence (Base _ ) = 12
  precedence (LBase _ ) = 12
  precedence (Const _ ) = 12
  precedence (Circ _ _ ) = 12
  precedence (Unit) = 12
  precedence (Star) = 12
  precedence (Box) = 12
  precedence (UnBox) = 12
  precedence (Revert) = 12
  precedence (RunCirc) = 12
  precedence (ExBox) = 12
  

  precedence (Set) = 12

  precedence (App _ _) = 10
  precedence (App' _ _) = 10  
  precedence (AppImp _ _) = 10
  precedence (AppType _ _) = 10
  precedence (AppDep _ _) = 10
  precedence (AppDict _ _) = 10
  precedence (AppTm _ _) = 10
  precedence (Pair _ _) = 11
  precedence (Arrow _ _) = 7
  precedence (Arrow' _ _) = 7
  precedence (Tensor _ _) = 8
  precedence (Bang _) = 9

  precedence (Pos p e) = precedence e
  precedence _ = 0


-- | Internal representations of declarations, they are obtained from
-- the concrete representation.  
data Decl = Object Position Id [Id]  -- ^ Object declaration, the list of
                                     -- identifiers are the instance names
                                     -- for the "Simple" and "SimpParam" classes. 
          | Data Position Id Exp [(Position, Id, Exp)] Id
            -- ^ Data type declaration, the last Id is the instance name for
            -- the "Parameter" class. 
          | SimpData Position Id Int Exp [(Position, Maybe Int, Id, Exp)] [Id]
            -- ^ Simple data type declaration, the list of
            -- identifiers are the instance names
            -- for the "Parameter", "Simple" and "SimpParam" classes. 
          | Class Position Id Exp Id Exp [(Position, Id, Exp, Exp)]
            -- ^ Class declaration.
          | Instance Position Id Exp [(Position, Id, Exp)]
            -- ^ Instance declaration.
          | Def Position Id Exp Exp
            -- ^ Function definition. 
          | TypeDef Position Id Exp Exp
            -- ^ Type definition
          | Defn Position Id (Maybe Exp) Exp
            -- ^ Function definition with only arguements annotated with types.
          | GateDecl Position Id (Maybe Exp) Exp
            -- ^ Gate declaration.
            
          | ControlDecl Position Id [Exp] Exp
            -- ^ Generalized controlled gate declaration.
            
          | Implicit Position Id Id Exp
            -- ^ Implicit type declaration. 
          | ImportDecl Position String
            -- ^ Import declaration.
          | OperatorDecl Position String Int String
            -- ^ Operator priority declaration.

-}
-- | Shape operation on terms and types
{-
shape Unit = Unit
shape Star = Star
shape (LBase x) | getIdName x == "Qubit" = Unit
shape a@(LBase x) | otherwise = a
shape a@(Base _) = a
shape a@(Const _) = a
shape a@(Var _) = a
shape a@(EigenVar _) = a
shape a@(GoalVar _) = a
shape a@(Bang _) = a
shape a@(Lift _) = a
shape a@(Circ _ _) = a
shape (Force m) = Force' (shape m)
shape (Force' m) = Force' (shape m)
shape (App t1 t2) = App' (shape t1) (shape t2)
shape (App' t1 t2) = App' (shape t1) (shape t2)
shape (AppDict t1 t2) = AppDict (shape t1) (shape t2)
shape (AppDep Box s) = AppDep' Box s
shape (AppDep a b) = AppDep' (shape a) (shape b)

shape (AppType a b) = AppType (shape a) b
shape (AppTm a b) = AppTm (shape a) (shape b)

shape (Tensor t1 t2) = Tensor (shape t1) (shape t2)
shape (Arrow t1 t2) = Arrow' (shape t1) (shape t2)
shape (Imply bds h) = Imply bds (shape h)
shape (Exists (Abst x t) t2) = Exists (abst x (shape t)) (shape t2)
shape (Forall (Abst x t) t2) = Forall' (abst x (shape t)) (shape t2)
shape a@(Forall' (Abst x t) t2) = a
shape (Pi (Abst x t) t2) = Pi' (abst x (shape t)) (shape t2)
shape (Label x) = Star
shape (Lam (Abst x t) cs) = Lam' (abst x (shape t)) 
shape (LamDep (Abst x t) cs) = LamDep' (abst x (shape t)) 
shape (LamType (Abst x t)) = LamType (abst x (shape t))
shape (LamTm (Abst x t)) = LamTm (abst x (shape t))
shape (LamDict (Abst x t)) = LamDict (abst x (shape t))
-- shape (LamImp (Abst x t)) = LamImp (abst x (shape t))
shape RunCirc = RunCirc
shape Box = Box
shape (Case tm (B br)) =
  Case (shape tm) (B (helper' br))
  where helper' ps =
          map (\ b -> open b $
                       \ ys m ->
                       abst ys (shape m))
          ps
shape a@(Wired _) = a
shape (Let m bd c) =
  let m' = shape m in
    open bd $ \ y b -> Let m' (abst y (shape b)) c

-- shape (LetAnn bd ty m c) =
--   let m' = shape m
--       ty' = shape ty
--   in
--     open bd $ \ y b -> LetAnn (abst y (shape b)) ty' m' c

shape (LetPair m bd cs) =
  let m' = shape m in
    open bd $ \ ys b -> LetPair m' (abst ys (shape b)) cs

shape (LetEx m bd cs) =
  let m' = shape m in
    open bd $ \ (y, z) b -> LetEx m' (abst (y, z) (shape b)) cs


shape (LetPat m bd) =
  let m' = shape m in
   open bd $ \ ps b ->  LetPat m' (abst ps (shape b))
shape (Pos _ e) = shape e
shape a = error $ "from shape: " ++ (show $ disp a)
-}

