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
               | LVarErr Variable Exp ZipCount Exp
               | CaseErr Exp (Maybe Exp) ZipCount
               | LamErr Exp Exp
               | ExistsErr Exp Exp
               | TensorErr Int Exp Exp
               | RetroErr Variable Exp
               | UnifErr Exp Exp
               | ExtendEnvErr [Either (NoBind Exp) Variable] Exp
               | DataErr Exp Exp
               | NotEq Exp Exp Exp
               | BangValue Exp Exp
               | MissBrErr Exp Exp
               | Vacuous Position [Variable] Exp Exp
               | NotParam Exp Exp
               | EvalErr EvalError

data EvalError = MissBranch Id Exp
               | UndefinedId Id 
               | PatternMismatch Pattern Exp
               | TupleMismatch [Variable] Exp

instance Disp EvalError where
  display flag (MissBranch id e) =
    text "missing branch for:" <+> display flag id $$
    text "when evaluating" $$
    nest 2 (display flag e)

  display flag (PatternMismatch p e) =
    text "Single pattern matching failure:" $$
    text "when matching:" $$
    nest 2 (display flag e) $$
    text "against:" $$
    nest 2 (display flag p)

  display flag (TupleMismatch xs e) =
    text "pattern matching on tuple fails:" $$
    text "when matching:" $$
    nest 2 (display flag e) $$
    text "against the tuple:" $$
    nest 2 (hsep $ punctuate comma $ map (display flag) xs)     

  display flag (UndefinedId id) =
    text "nontermination detected when evaluating:" <+> display flag id


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


  display flag (LVarErr x m c t) =
    text "the linear variable:" <+> display flag x $$
    text "is used nonlinearly in:" $$
    nest 2 (display flag m) $$
    text "the count:" <+> display flag c $$
    text "it has type:" <+> display flag t


  display flag (CaseErr m a count) =
    text "nonlinear use of" <+> quotes (display flag m) <+> text "due to branching in" $$
    nest 2 (display flag a) $$
    text "the count:" <+> display flag count


  display flag (LamErr a t) =
    text "the term:" $$
    nest 2 (display flag a) $$
    text "has an arrow type, but it is expected to have type:" $$
    nest 2 (display flag t) 


  display flag (ExistsErr m a) =
    text "expecting an existential type for" $$
    nest 2 (display flag m) $$
    text "but actual type is:" $$
    nest 2 (display flag a)


  display flag (TensorErr n a t) =
    text "the term:" <+> display flag a $$
    text "is expected to have a multi-tensor type of arity:" <+> int n $$ 
    text "but it has the type:" $$
    nest 2 (display flag t)


  display flag (RetroErr x tm) =
    text "retroactive dependent pattern matching on the variable:" <+> display flag x 
    $$ text "it is currently equals to:" $$
    nest 2 (display flag tm)

  display flag (UnifErr t1 t2) =
    text "cannot unify the type:" $$
    nest 2 (display flag t1) $$
    text "with the type:" $$
    nest 2 (display flag t2)

  display flag (ExtendEnvErr vs b) =
    text "error when extending variables:" <+> hsep (map (display flag) vs) $$
    text "with type:" <+> display flag b

  display flag (DataErr t tm) = 
    text "the term:" $$
    nest 2 (display flag tm) $$
    text "is expected to have a data type, but it has type:" $$
    nest 2 (display flag t)


  display flag (BangValue a ty) =
    text "Expecting a value form of the type" $$
    nest 2 (display flag ty) $$
    text "actual form:" $$
    nest 2 (display flag a) $$
    text "Suggestion: try eta-expansion on the above term"


  display flag (NotEq a q t) =
    text "the program:" $$
    nest 2 (display flag a) $$
    text "is expected to have type:" $$
    nest 2 (display flag q) $$
    text "but it has type:" $$
    nest 2 (display flag t)


  display flag (MissBrErr t a) =
    text "Normalization error:" $$ 
    text "missing a branch for" $$ 
    nest 2 (display flag t) $$ 
    text "when evaluating" $$ nest 2 (display flag a)

  display flag (Vacuous p vs ty m) =
    display flag p <+> text "the following variables are vacuously quantified:" $$
    nest 2 (hsep (map (display flag) vs)) $$
    text "they have type:" $$
    nest 2 (display flag ty) $$
    text "their scope:" $$
    nest 2 (display flag m) $$
    text "note that the variables in the type constraints does not count toward their occurrences "
    
  display flag (NotParam m a) =
    text "expecting a parameter type for" $$
    nest 2 (display flag m) $$
    text "but the actual type is:" $$
    nest 2 (display flag a) $$
    text "suggestion: use ! on the type to indicate reusability"

  display flag (EvalErr e) =
    text "evaluation error:" $$ display flag e
