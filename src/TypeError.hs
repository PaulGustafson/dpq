module TypeError where

import Utils
import Syntax
import qualified ConcreteSyntax as C


import Nominal
import Prelude hiding ((<>))
import Text.PrettyPrint
import Control.Monad.Except


data TypeError = Unhandle Exp
               | ErrPos Position TypeError
               | NoDef Id
               | UnBoundErr Variable
               | KAppErr Exp Exp Exp
               | ArrowErr Exp Exp
               | NotAValidClass Exp
               | ForallLinearErr [Variable] Exp
               | KArrowErr Exp Exp
               | LiftErrVar Variable Exp Exp

                 
-- | Add a position to an error message if the message does not already contain
addErrPos p a@(ErrPos _ _) = a
addErrPos p a = ErrPos p a


instance Disp TypeError where
  display flag (ErrPos p e) =
    display flag p $$   
    display flag e

  display flag (Unhandle t) =
    text "there is no type inference rule to infer a type for the expresson:" $$
    nest 2 (display flag t)

  display flag (NoDef t) =
    text "no definition for the identifier:" $$ nest 2 (display flag t)

  display flag (UnBoundErr x) =
    text "unbound variable:" <+> display flag x

  display flag (KAppErr ty b a) =
    text "the type:" $$
    nest 2 (display flag ty) $$
    text "is expected to have an arrow kind, but it has kind:" $$
    nest 2 (display flag a) $$
    text "in the type expression:" $$
    nest 2 (display flag b)

  display flag (ArrowErr ty b) =
    text "the term:" $$
    nest 2 (display flag ty) $$
    text "is expected to have an arrow type, but it has type:" $$
    nest 2 (display flag b) 

  display flag (NotAValidClass h) =
    text "the type class constraint:" $$
    (nest 2 $ display flag h) $$
    text "is not a valid type class constraint."


  display flag (ForallLinearErr xs ty) =
    text "irrelavent quantification on linear resource:"$$
    nest 2 (hsep $ map (display flag) xs) $$
    text "have a linear type:" $$
    nest 2 (display flag ty)


  display flag (KArrowErr ty a) =
    text "the type:" $$
    nest 2 (display flag ty) $$
    text "has an arrow kind, but it is expected to have kind:" $$
    nest 2 (display flag a) 

  display flag (LiftErrVar x t tt) =
    text "there is a linear resources:" <+> display flag x $$
    text "of the type:" $$
    nest 2 (display flag tt ) $$
    text "when lifting the term:" $$
    nest 2 (display flag t)
