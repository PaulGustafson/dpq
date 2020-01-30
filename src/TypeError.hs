-- | This module defines the error data type and its 'Disp' instance for type checking.

module TypeError where

import Utils
import Syntax
import Simulation
import SyntacticOperations
import qualified ConcreteSyntax as C


import Nominal
import Prelude hiding ((<>))
import Text.PrettyPrint
import Control.Monad.Except

-- | A data type for typing error.
data TypeError = Unhandle Exp
               | ErrPos Position TypeError
               | NoDef Id
               | UnBoundErr Variable
               | KAppErr Exp Exp Exp
               | ArrowErr Exp Exp
               | NotAValidClass Exp
               | ForallLinearErr [Variable] Exp Exp
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
               | EvalErr EvalError -- ^ A wrapper for evaluation error.
               | Originated Exp TypeError
               | ResolveErr Exp
               | ErrDoc Doc
               | TypeClassNotValid Exp
               | MethodsErr [Id] [Id]
               | InstanceOverlap Exp Id Exp
               | NotAParam Exp
               | NotStrictSimple Exp
               | GateErr Position Id
               | Ambiguous Id
               | IndexInconsistent Int Int Id
               | CoverErr [Id] [Id] Id
               | NonSimplePatErr Exp
               | SubtermErr Exp Exp
               | NotSimple Exp
               | TConstrErr Id
               | TyAmbiguous (Maybe Id) Exp               
               | BangErr Exp Exp
               | PfErrWrapper Exp TypeError Exp
               -- ^ A wrapper for proof checking error.
               | TensorExpErr Exp Exp
               | NotUnit
               | ImplicitCase Variable Exp
               | ImplicitVarErr Variable Exp
               | LamInferErr Exp
               | ArityExistsErr Exp [Variable]
               deriving Show

-- | A data type for evaluation errors.
data EvalError = MissBranch Id Exp
               | UndefinedId Id 
               | PatternMismatch Pattern Value
               | TupleMismatch [Variable] Value
               | ErrWrapper TypeError
               | SimulationErr SimulateError
               deriving Show                 
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

  display flag (SimulationErr a) =
    display flag a

  -- A wrapper due to tcToEval
  display flag (ErrWrapper e) = display flag e

-- | Add a position to an error message if the message does not already contain
-- position information.
addErrPos :: Position -> TypeError -> TypeError
addErrPos p a@(ErrPos _ _) = a
addErrPos p a = ErrPos p a


instance Disp TypeError where
  display flag (ErrPos p e) =
    display flag p $$   
    display flag e

  display flag (Unhandle t) =
    text "there is no type inference rule to infer a type for the expresson:" $$
    nest 2 (display flag t) 
--    text "suggestion: add a type annotation"

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


  display flag (ForallLinearErr xs ty exp) =
    text "illegal quantification on linear resource:"$$
    nest 2 (hsep $ map (display flag) xs) $$
    text "have a linear type:" $$
    nest 2 (display flag ty) $$
    text "when checking:" $$ display flag exp


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


  display flag (Originated o e) =
    let p = obtainPos o
    in case p of
         Nothing ->  display flag e $$ text "from a use of" $$ nest 2 (display flag o)
         Just p ->  display flag e $$ text "from a use of" $$ nest 2 (display flag o) $$ text "at" <+> display flag p


  display flag (ResolveErr e) =
    text "can't resolve the constraint: " $$
    (nest 2 $ display flag e)

  display flag (ErrDoc e) = e

  display flag (TypeClassNotValid h) =
    text "the type class constraint" $$
    (nest 2 $ display flag h) $$
    text "is not a valid type class constraint."

  display flag (MethodsErr [] act) =
    text "does not expect to implement any method, " $$
    text "but methods implemented: " $$
    nest 2 (hsep $ punctuate comma (map (display flag) act))
  display flag (MethodsErr exp []) =
    text "expected to implement all of the following methods in the exact order: " $$
    nest 2 (hsep $ punctuate comma (map (display flag) exp)) $$
    text "but no method is implemented"
  display flag (MethodsErr exp act) =
    text "expected to implement all of the following methods in the exact order: " $$
    nest 2 (hsep $ punctuate comma (map (display flag) exp)) $$
    text "actual methods implemented: " $$
    nest 2 (hsep $ punctuate comma (map (display flag) act)) 

  display flag (InstanceOverlap h id exp) =
    text "instance head:" <+> display flag h $$
    text "is overlapped with existing instance:" $$
    nest 2 (display flag exp) $$
    text "instance info:" <+> disp id

  display flag (NotAParam exp) =
    text "the expression:" <+> display flag exp $$
    text "is not a parameter type"

  display flag (NotStrictSimple e) =
    text "the type expression:" <+> display flag e $$
    text "is not a strictly simple type" $$
    text "i.e. composed only from object types and tensor"
    
  display flag (GateErr p g) =
    display flag p $$ text "the gate:" <+> display flag g $$
    text "must have at least one wired input"

  display flag (Ambiguous id) =
    text "ambiguous declarations" $$
    (text "in the simple type declaration for:" <+> display flag id)

  display flag (IndexInconsistent i j d) =
    (text ("expected pattern matching on the "++show (i+1)++"th argument")) $$
    (text ("but there is also pattern matching on the "++show (j+1)++"th argument")) $$
    text "in the definition for:" <+> display flag d $$
    text "Note that in the Simple type declaration" $$
    text "we can only pattern match on a fixed argument"


  display flag (CoverErr actual expect d) =
    text "coverage error during the simple check"$$
    text "need to cover exactly the following constructors:" $$
    nest 2 (hsep $ punctuate comma (map (display flag) expect)) $$
    text "the actual covering is the following:" $$
    nest 2 (hsep $ punctuate comma (map (display flag) actual)) $$
    text "in the definition for:" <+> display flag d


  display flag (NonSimplePatErr b) =
    text "expecting a variable in the pattern, but get:" <+> display flag b

  display flag (SubtermErr b h) =
    text "the expression:" <+> display flag b $$
    text "is not structurally smaller than:" <+> display flag h

  display flag (NotSimple e) =
    text "the type expression:" <+> display flag e $$
    text "is not a simple type"

  display flag (TConstrErr id) =
    text "unexpected type constructor:" <+> display flag id $$
    text "during the simplicity checking"

  display flag (TyAmbiguous Nothing ty) =
    text "infer a type that contains free variables:" $$
    nest 2 (display flag ty) 


  display flag (TyAmbiguous (Just f) ty) =
    text "infer a type that contains free variables:" $$
    nest 2 (display flag ty) $$
    text "for the definition:" <+> display flag f


  display flag (BangErr t b) =
    text "the term:" $$
    nest 2 (display flag t) $$
    text "is expected to have a bang type, but it has type:" $$
    nest 2 (display flag b)

  display flag (TensorExpErr a t) =
    text "the term:" <+> display flag a $$
    text "has a tensor type, but it is expected to have type:" $$
    nest 2 (display flag t)

  display flag (NotUnit) =
    text "controlled gate's type can not contain unit" 


  display flag (ImplicitCase x ann) =
    text "the irrelavent pattern variable:" <+> dispRaw x $$   
    text "is used explicitly in the annotated program:" $$
    nest 2 (dispRaw ann)

  display flag (ImplicitVarErr x a) =
    text "the irrelavent variable: "
    <+> display flag x $$
    text "is used explicitly in the annotated program:" $$
    nest 2 (display flag a)

  display flag (LamInferErr a) =
    text "cannot infer a type for lambda abstraction: "
    <+> display flag a $$
    text "suggestion: add a type annotation" 

  display flag (ArityExistsErr at xs) =
    text "unexpected pair pattern for existential type." $$
    text "when checking:" <+> hsep (map (display flag) xs) $$
    text "againts:" <+> display flag at
    
  display flag a = error $ "from display TypeError:" ++ show a 
