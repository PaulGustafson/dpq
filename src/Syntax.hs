{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleInstances, RankNTypes, GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass, PatternSynonyms, ViewPatterns, ApplicativeDo #-}

{-|
This module describes the abstract syntax of dpq. We use Peter Selinger's
nominal library to handle the affair of binding in abstract syntax.
Please see <http://hackage.haskell.org/package/nominal here> for
the documentation of nominal library.
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



-- | The core abstract syntax tree for dpq expression. We use prime ' to indicate 
-- the given constructor belongs to the parameter fragment. The core syntax contains
-- the surface syntax and other forms of annotations for proof checking.
data Exp =
  Var Variable
  | EigenVar Variable
  | GoalVar Variable
    -- User defined constant
  | Const Id
  | LBase Id
  | Base Id
    -- Arrows
  | Lam (Bind [Variable] Exp) 
  | Lam' (Bind [Variable] Exp)

  | Arrow Exp Exp
  | Arrow' Exp Exp
    
  | App Exp Exp
  | App' Exp Exp

    -- Dictionary abstraction and application.  
  | AppDict Exp Exp
  | Imply [Exp] Exp
  | LamDict (Bind [Variable] Exp)

    -- Pair and existential  
  | Tensor Exp Exp 
  | Pair Exp Exp
  | Let Exp (Bind Variable Exp) 
  | LetPair Exp (Bind [Variable] Exp)
  | LetPat Exp (Bind Pattern Exp)
  | Exists (Bind Variable Exp) Exp
  | Case Exp Branches

    -- Lift and force  
  | Bang Exp
  | Force Exp
  | Force' Exp
  | Lift Exp

    -- Circuit operations  
  | Box
  | ExBox
  | UnBox
  | RunCirc
  | Revert 
  | Circ Exp Exp
    
    -- constants  
  | Star
  | Unit
  | Set 
  | Sort

    -- Dependent types
  | Pi (Bind [Variable] Exp) Exp
  | Pi' (Bind [Variable] Exp) Exp
    
  | PiImp (Bind [Variable] Exp) Exp
  | PiImp' (Bind [Variable] Exp) Exp

  | LamDep (Bind [Variable] Exp)
  | LamDep' (Bind [Variable] Exp)

  | AppDep Exp Exp
  | AppDep' Exp Exp

  -- explicit type abstraction and application
  | LamDepTy (Bind [Variable] Exp)
  | AppDepTy Exp Exp

  -- Annotated lambda, this makes infering body using infer mode.
  | LamAnn Exp (Bind [Variable] Exp)
  | LamAnn' Exp (Bind [Variable] Exp)

  -- Annotated term  
  | WithType Exp Exp

  -- Irrelavent quantification  
  | Forall (Bind [Variable] Exp) Exp    
  | LamType (Bind [Variable] Exp)
  | LamTm (Bind [Variable] Exp)
  | AppType Exp Exp 
  | AppTm Exp Exp  
  -- others.  
  | PlaceHolder
  | Pos Position Exp
  deriving (Eq, Generic, Nominal, NominalShow, NominalSupport, Show)

-- | Branches for case expressions.
data Branches = B [Bind Pattern Exp]
              deriving (Eq, Generic, Show, NominalSupport, NominalShow, Nominal)

-- | Pattern can a bind term variable or a type variable, or have an instantiation (Left)
-- that is bound at a higher-level. 
data Pattern = PApp Id [Either (NoBind Exp) Variable] 
             deriving (Eq, Generic, NominalShow, NominalSupport, Nominal, Bindable, Show)



instance Disp Pattern where
  display flag (PApp id vs) =
    display flag id <+>
    hsep (map helper vs) 
    where helper (Left (NoBind x)) =
            braces $ display flag x
          helper (Right x) = display flag x 

-- | A helper function for display various of applications. 
dispAt b s =
  if b then text "" else text ("@"++s)

instance Disp Exp where
  display flag (Var x) = display flag x
  display flag (GoalVar x) =
    if flag then disp x else braces $ dispRaw x
  display flag (EigenVar x) =
    if flag then disp x else brackets $ dispRaw x
  display flag (Const id) = display flag id
  display flag (LBase id) = display flag id
  display flag (Base id) = display flag id
  display flag (Pos _ e) = display flag e
  display flag (Lam bds) =
    open bds $ \ vs b ->
    fsep [text "\\" , (hsep $ map (display flag) vs), text ".", nest 2 $ display flag b]
  display flag (LamAnn ty bds) =
    open bds $ \ vs b ->
    fsep [text "\\(" , hsep $ map (display flag) vs, text "::", display flag ty,  text ").", nest 2 $ display flag b]

  display flag (LamAnn' ty bds) =
    open bds $ \ vs b ->
    fsep [text "\\'(" , hsep $ map (display flag) vs, text "::", display flag ty,  text ").", nest 2 $ display flag b]

  display flag (Lam' bds) =
    open bds $ \ vs b ->
    fsep [text "\\'" , (hsep $ map (display flag) vs), text ".", nest 2 $ display flag b]
  display flag (LamDict bds) =
    open bds $ \ vs b ->
    fsep [text "\\dict" , (hsep $ map (display flag) vs), text ".", nest 2 $ display flag b]    
  display flag (LamTm bds) =
    open bds $ \ vs b ->
    fsep [text "\\tm" , (hsep $ map (display flag) vs) <+> text ".", nest 2 $ display flag b]
    
  display flag (LamDep bds) =
    open bds $ \ vs b ->
    fsep [text "\\dep" , (hsep $ map (display flag) vs) <+> text ".", nest 2 $ display flag b]

  display flag (LamDepTy bds) =
    open bds $ \ vs b ->
    fsep [text "\\depTy" , (hsep $ map (display flag) vs) <+> text ".", nest 2 $ display flag b]

  display flag (LamDep' bds) =
    open bds $ \ vs b ->
    fsep [text "\\dep'" , (hsep $ map (display flag) vs) <+> text ".", nest 2 $ display flag b]
    
  display flag (LamType bds) =
    open bds $ \ vs b ->
    fsep [text "\\ty" , (hsep $ map (display flag) vs) <+> text ".", nest 2 $ display flag b]

  display flag (Forall bds t) =
    open bds $ \ vs b ->
    fsep [text "forall", parens ((hsep $ map (display flag) vs) <+> text "::" <+> display flag t) <+> text ".", nest 5 $ display flag b]

  display flag a@(App t t') = 
     fsep [dParen flag (precedence a - 1) t, dParen flag (precedence a) t']

  display flag a@(AppType t t') =
    fsep [dParen flag (precedence a - 1) t, dispAt flag "AppType", dParen flag (precedence a) t']

  display flag a@(App' t t') =
    fsep [dParen flag (precedence a - 1) t, dispAt flag "App'", dParen flag (precedence a) t']

  display flag (WithType m t) =
    fsep [text "withType" <+> display flag t <+> text ":", display flag m]

  display flag a@(AppDep t t') =
       fsep [dParen flag (precedence a - 1) t, dispAt flag "AppDep",
             dParen flag (precedence a) t']

  display flag a@(AppDepTy t t') =
       fsep [dParen flag (precedence a - 1) t, dispAt flag "AppDepTy",
             dParen flag (precedence a) t']

  display flag a@(AppDep' t t') =
    fsep [dParen flag (precedence a - 1) t, dispAt flag "AppDep'", dParen flag (precedence a) t']
    
  display flag a@(AppDict t t') =
    fsep [dParen flag (precedence a - 1) t, dispAt flag "AppDict", dParen flag (precedence a) t']
    
  display flag a@(AppTm t t') =
     fsep [dParen flag (precedence a - 1) t, dispAt flag "AppTm", dParen flag (precedence a) t']
    
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
    
  display flag (Force m) = text "&" <> display flag m
  display flag (Force' m) = text "&'" <> display flag m
  display flag (Lift m) = text "lift" <+> display flag m

  display flag (Circ u t) =
    text "Circ" <> (parens $ fsep [display flag u <> comma, display flag t])
  display flag (Pi bd t) =
    open bd $ \ vs b ->
    fsep [parens ((hsep $ map (display flag) vs) <+> text "::" <+> display flag t)
    <+> text "->" , nest 2 $ display flag b]

  display flag (PiImp bd t) =
    open bd $ \ vs b ->
    fsep [braces ((hsep $ map (display flag) vs) <+> text "::" <+> display flag t)
    <+> text "->" , nest 2 $ display flag b]

  display flag (PiImp' bd t) =
    open bd $ \ vs b ->
    fsep [braces ((hsep $ map (display flag) vs) <+> text "::" <+> display flag t)
    <+> text "->'" , nest 2 $ display flag b]

  display flag (Pi' bd t) =
    open bd $ \ vs b ->
    fsep [parens ((hsep $ map (display flag) vs) <+> text "::" <+> display flag t)
    <+> text "->'" , nest 2 $ display flag b]
    
  display flag (Exists bd t) =
    open bd $ \ v b ->
    fsep [text "exists" <+> display flag v <+> text "::" <+> display flag t,
           text "." , nest 2 $ display flag b]    
  display flag (Box) = text "box"
  display flag (ExBox) = text "existsBox"
  display flag (UnBox) = text "unbox" 
  display flag (Revert) = text "revert"
  display flag (RunCirc) = text "runCirc"
  display flag (Let m bd) =
    open bd $ \ x b ->
    fsep [text "let" <+> display flag x <+> text "=", display flag m,
          text "in" <+> display flag b]
    
  display flag (LetPair m bd) =
    open bd $ \ xs b ->
    fsep [text "let" <+> parens (hsep $ punctuate comma $ map (display flag) xs),
          text "=", display flag m,
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

  display flag e = error $ "from display: " ++ show e

  precedence (Var _ ) = 12
  precedence (GoalVar _ ) = 12
  precedence (EigenVar _ ) = 12
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

instance NominalShow (NoBind Exp) where
  showsPrecSup sup d (NoBind x) = showsPrecSup sup d x

instance Disp (Either (NoBind Exp) Variable) where
  display flag (Left (NoBind e)) = braces $ display flag e
  display flag (Right x) = display flag x


-- | The value domain, for evaluation purpose.  
data Value =
  VLabel Label
  | VVar Variable -- ^ For the parameters and generic control in a gate. 
  | VConst Id
  | VTensor Value Value
  | VUnit
  | VLBase Id
  | VBase Id
  | VLam (Bind LEnv (Bind [Variable] Exp)) -- ^ Lambda forms a closure.
  | VPair Value Value
  | VStar
  | VLift (Bind LEnv Exp) -- ^ Lift also forms a closure.
  | VLiftCirc (Bind [Variable] (Bind LEnv Exp))
    -- ^ Circuit binding, [Variable] is like a lambda that handles parameter arguments
    -- and the control argument, LEnv binds a variable to a circuit.
  | VCircuit Morphism
    -- ^ Unbound circuit (incomplete). 
  | Wired (Bind [Label] Value)
    -- ^ Complete circuit.
  | VApp Value Value
  | VForce Value
  | VBox
  | VExBox
  | VUnBox
  | VRevert
  | VRunCirc
  deriving (Show, NominalShow, NominalSupport, Generic)

-- | Local value environment for evaluation. 
type LEnv = Map Variable Value

instance Bindable (Map Variable Value) where
  binding loc = do
    loc' <- map_binding (Map.toList loc)
    pure $ Map.fromList loc'
      where
        map_binding [] = pure []
        map_binding ((k,v):t) = do
          k' <- binding k
          v' <- nobinding v
          t' <- map_binding t
          pure ((k',v'):t')  

-- | Gate, [Value] is a list of parameters, the last three values
-- are input, output and control.          
data Gate = Gate Id [Value] Value Value Value
  deriving (Show, NominalShow, NominalSupport, Generic)

type Gates = [Gate]

-- | Morphism denotes an incomplete circuit, a completion would be
-- using the Wired constructor to bind all the free labels in it.
data Morphism = Morphism Value Gates Value
  deriving (Show, NominalShow, NominalSupport, Generic)
           
instance Nominal Gate where
  pi • Gate id params v1 v2 ctrl = Gate id (pi • params) (pi • v1) (pi • v2) (pi • ctrl)

instance Nominal Morphism where
  pi • Morphism v1 gs v2 = Morphism (pi • v1) (pi • gs) (pi • v2)

instance Nominal Value where
  pi • VLabel l = VLabel $ pi • l
  pi • VVar x = VVar $ pi • x
  pi • VLam bd = VLam $ pi • bd
  pi • Wired bd = Wired $ pi • bd
  pi • VConst id = VConst id
  pi • VLBase id = VLBase id
  pi • VBase id = VBase id
  pi • VUnit = VUnit
  pi • VStar = VStar
  pi • VLift bd = VLift $ pi • bd
  pi • VLiftCirc bd = VLiftCirc $ pi • bd
  pi • VTensor a b = VTensor (pi • a) (pi • b)
  pi • VPair a b = VPair (pi • a) (pi • b)
  pi • VApp a b = VApp (pi • a) (pi • b)
  pi • VForce v = VForce (pi • v)
  pi • VCircuit m = VCircuit (pi • m)
  pi • VBox = VBox
  pi • VExBox = VExBox
  pi • VRevert = VRevert
  pi • VRunCirc = VRunCirc 
  pi • VUnBox = VUnBox

  
instance Disp Value where
  display flag (VLabel l) = text $ show l
  display flag (VVar l) = text $ show l
  display flag (VLBase id) = display flag id
  display flag (VBase id) = display flag id
  display flag (VConst id) = display flag id
  display flag (VTensor x y) = display flag x <+> text "*" <+> display flag y
  display flag (VPair x y) = parens $ display flag x <+> text "," <+> display flag y
  display flag (VUnit) = text "Unit"
  display flag (VStar) = text "()"
  display flag (VBox) = text "box"
  display flag (VExBox) = text "existsBox"
  display flag (VUnBox) = text "unbox"
  display flag (VRevert) = text "revert"
  display flag (VRunCirc) = text "runCirc"
  display flag (VCircuit m) = display flag m
  display flag (VLam (Abst env (Abst vs e))) = 
    text "vlam" <+> braces (display flag env) $$
    sep [text "\\", hsep (map (display flag) vs) , text ".", nest 2 (display flag e)]
  display flag (VLift (Abst env e)) = 
    text "vlift" <+> braces (display flag env) $$ nest 2 (display flag e)
  display flag (VLiftCirc (Abst vs (Abst env e))) =
    text "vliftCirc" <+> hsep (map (display flag) vs) <+> text "." <+> braces (display flag env) $$ nest 2 (display flag e)
  display flag (Wired (Abst ls v )) = display flag v
  display flag (VApp v1 v2) = parens $ display flag v1 <+> display flag v2  
  display flag (VForce v) = text "&" <+> display flag v

instance Disp (Map Variable Value) where
   display flag l =
     vcat $
     map (\ (x, y) -> display flag x <+> text ":=" <+> display flag y) (Map.toList l)
   
instance Disp Morphism where
  display flag (Morphism ins gs outs) =
    (braces $ display flag ins) $$
    nest 2 (vcat $ map (display flag) gs) $$
    (braces $ display flag outs) 

instance Disp Gate where
  display flag (Gate g params ins outs ctrls) =
    display flag g <+> brackets (hsep $ punctuate comma (map (display flag) params))
    <+> (braces $ (display flag ins)) <+> (braces $ (display flag outs))
    <+> (brackets $ display flag ctrls)

-- | Convert a 'basic value' from the value domain to an expression,
-- so that the type checker can take advantage of cbv.   
toExp :: Value -> Exp
toExp (VConst id) = Const id
toExp VStar = Star
toExp (VApp a b) = App (toExp a) (toExp b)
toExp (VPair a b) = Pair (toExp a) (toExp b)

-- | Declarations in abstract syntax, resolved from the declarations
-- in the concrete syntax. 
data Decl = Object Position Id
            
          | Data Position Id Exp [(Position, Id, Exp)]
            -- ^ Id: the type constructor, Exp: a kind expression, [(Position, Id, Exp)]:
            -- the list of data constructors with corresponding types. 
          | SimpData Position Id Int Exp [(Position, Maybe Int, Id, Exp)]
            -- ^ Id: the type constructor, Int: the number of type arguments,
            -- Exp: partial kind annotation. In [(Position, Maybe Int, Id, Exp)],
            -- Maybe Int: the position where dependent pattern matching is performed.
            -- Id: data constructor, Exp: pretypes for the data constructors, to
            -- be further processed. 
          | Class Position Id Exp Id Exp [(Position, Id, Exp)]
            -- ^ Id: class name, Exp: instance function type,
            -- [(Position, Id, Exp)]: list of methods and their definitions.
          | Instance Position Id Exp [(Position, Id, Exp)]
            -- ^ Id: instance function name, Exp: instance function type,
            -- [(Position, Id, Exp)]: list of methods and their definitions.
          | Def Position Id Exp Exp
            -- ^ Function declaration, Id: name, Exp: type, Exp: definition
          | GateDecl Position Id [Exp] Exp
          | ControlDecl Position Id [Exp] Exp
          | ImportDecl Position String
          | OperatorDecl Position String Int String
          | Defn Position Id (Maybe Exp) Exp
            -- ^ Function declaration in infer mode, Id: name, May Exp: maybe a partial type,
            -- Exp: definition

