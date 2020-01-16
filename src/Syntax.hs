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

import Control.Monad.Identity
import Control.Monad.Except
import Text.PrettyPrint
import qualified Data.Map as Map
import qualified Data.Set as S
import Data.Map (Map)

import Data.List
import Debug.Trace




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
  | PiImp (Bind [Variable] Exp) Exp
  | PiImp' (Bind [Variable] Exp) Exp
  | LamAnn Exp (Bind [Variable] Exp)
  | LamAnn' Exp (Bind [Variable] Exp) 
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
  | AppDepTy Exp Exp
  | AppDep' Exp Exp
  | PlaceHolder
  | WithType Exp Exp
  | Pos Position Exp
  deriving (Eq, Generic, Nominal, NominalShow, NominalSupport, Show)


-- | Gate <name> <params> <in> <out> <ctrls>
data Gate = Gate Id [Exp] Exp Exp Exp
          deriving (Eq, Generic, NominalSupport, NominalShow, Nominal, Show)

type Gates = [Gate]

-- | (a, Cs, b)
data Morphism = Morphism Exp Gates Exp
              deriving (Eq, Generic, NominalSupport, NominalShow, Nominal, Show)

data Branches = B [Bind Pattern Exp]
              deriving (Eq, Generic, Show, NominalSupport, NominalShow, Nominal)

-- | patterns bind only term variables
data Pattern = PApp Id [Either (NoBind Exp) Variable] 
             deriving (Eq, Generic, NominalShow, NominalSupport, Nominal, Bindable, Show)



instance Disp Pattern where
  display flag (PApp id vs) =
    display flag id <+>
    hsep (map helper vs) 
    where helper (Left (NoBind x)) =
            braces $ display flag x
          helper (Right x) = display flag x 

instance Disp Morphism where
  display b (Morphism ins gs outs) =
    (braces $ display b ins) $$
    nest 2 (vcat $ map (display b) gs) $$
    (braces $ display b outs) 

instance Disp Gate where
  display flag (Gate g params ins outs ctrls) =
    disp g <+> brackets (hsep $ punctuate comma (map (display flag) params))
    <+> (braces $ display flag ins) <+> (braces $ display flag outs) <+> (brackets $ display flag ctrls)


instance Disp Exp where
  display flag (Var x) = display flag x
  display flag (Label x) = display flag x
  display flag (GoalVar x) = braces $ display flag x
  display flag (EigenVar x) = brackets (display flag x)
  display flag (Const id) = display flag id
  display flag (LBase id) = display flag id
  display flag (Base id) = display flag id
  display flag (Pos _ e) = display flag e
  display flag (Lam bds) =
    open bds $ \ vs b ->
    fsep [text "\\" , (hsep $ map (display flag) vs), text ".", nest 2 $ display flag b]
  display flag (LamAnn ty bds) =
    open bds $ \ vs b ->
    fsep [text "\\" , parens (hsep $ map (display flag) vs), text "::", display flag ty,  text ".", nest 2 $ display flag b]

  display flag (LamAnn' ty bds) =
    open bds $ \ vs b ->
    fsep [text "\\'" , parens (hsep $ map (display flag) vs), text "::", display flag ty,  text ".", nest 2 $ display flag b]

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
    fsep [dParen flag (precedence a - 1) t, dParen flag (precedence a) t']
--    fsep [dParen flag (precedence a - 1) t, text "@2", dParen flag (precedence a) t']
  display True a@(App' t t') =
    fsep [dParen True (precedence a - 1) t, text "@", dParen True (precedence a) t']
    
  display False a@(App' t t') =
    fsep [dParen False (precedence a - 1) t, text "@", dParen False (precedence a) t']

  display flag (WithType m t) =
    fsep [text "withType" <+> display flag t <+> text ":", display flag m]


  display flag a@(AppDep t t') =
       fsep [dParen flag (precedence a - 1) t, dParen flag (precedence a) t']
--    fsep [text "@0", dParen flag (precedence a - 1) t, dParen flag (precedence a) t']
  display flag a@(AppDepTy t t') =
       fsep [dParen flag (precedence a - 1) t, dParen flag (precedence a) t']

  display flag a@(AppDep' t t') =
    fsep [dParen flag (precedence a - 1) t, dParen flag (precedence a) t']
--    fsep [dParen flag (precedence a - 1) t, text "@", dParen flag (precedence a) t']
    
  display flag a@(AppDict t t') =
    fsep [dParen flag (precedence a - 1) t, dParen flag (precedence a) t']
--    fsep [text "@4", dParen flag (precedence a - 1) t, dParen flag (precedence a) t']
    
  display flag a@(AppTm t t') =
     fsep [dParen flag (precedence a - 1) t, dParen flag (precedence a) t']
--    fsep [text "@5", dParen flag (precedence a - 1) t, dParen flag (precedence a) t']
    
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

  display flag (LetEx m bd) =
    open bd $ \ (x, y) b ->
    fsep [text "let" <+> braces (display flag x<>comma<+> display flag y)
          <+> text "=", display flag m,
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

  display flag (Wired bd) = 
   open bd $ \ wires e -> (display flag e)

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


data Decl = Object Position Id
          | Data Position Id Exp [(Position, Id, Exp)] 
          | SimpData Position Id Int Exp [(Position, Maybe Int, Id, Exp)] 
          | Class Position Id Exp Id Exp [(Position, Id, Exp)]
          | Instance Position Id Exp [(Position, Id, Exp)]
          | Def Position Id Exp Exp
          | GateDecl Position Id [Exp] Exp
          | ControlDecl Position Id [Exp] Exp
          | ImportDecl Position String
          | OperatorDecl Position String Int String
          | Defn Position Id (Maybe Exp) Exp

