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
