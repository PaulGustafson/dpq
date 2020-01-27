-- | The concrete syntax for the surface language. It will
-- be resolved into abstract syntax. 


module ConcreteSyntax where
import Utils
import Text.PrettyPrint
import Text.Parsec.Pos
import Data.List
import Prelude hiding((<>))


  

data Exp =
  Base String 
  | Var String
  | Set 
  | Star
  | Unit
  | Arrow Exp Exp
  | Imply [Exp] Exp
  | Tensor Exp Exp 
  | Bang Exp
  | Circ Exp Exp
  | Pi [String] Exp Exp
  | PiImp [String] Exp Exp
  | Exists String Exp Exp
  | Forall [([String], Exp)] Exp
  | Lam [String] Exp
  | LamAnn [String] Exp Exp
  | App Exp Exp
  | Pair Exp Exp
  | Let [Binding] Exp
  | Box
  | ExBox
  | UnBox
  | Revert
  | RunCirc
  | Case Exp Branches
  | Wild
  | Pos Position Exp
  | WithAnn Exp Exp
  deriving (Show, Eq)

-- | Branches for case expression, must be of the form:
-- C x y z -> e, where x, y, z are variables.
type Branches = [(String, [Exp], Exp)]

-- | Binding for let expression. The type declaration for let (BAnn) will be
-- translated away. 
data Binding =
  BSingle (String, Exp)
  | BPair ([String], Exp)
  | BPattern (String, [Exp], Exp)
  | BAnn (String, Exp, Exp)
  deriving (Show, Eq)


data Decl = GateDecl Position String [Exp] Exp
            -- ^ Gate declaration, [Exp] are the parameters for the gate. 
          | ControlDecl Position String [Exp] Exp
            -- ^ Generic control gate declaration, [Exp] are the parameters. 
          | Object Position String
          | Def Position String Exp [String] Exp
            -- ^ Funtion definition, [String] are the arguments.
          | Defn Position String [Either Exp ([String], Exp)]
            [Either Exp ([String], Exp)] Exp
            -- ^ Infer mode function definition, the first [Either Exp ([String], Exp)]
            -- are the irrelevant arguments, the second are the explicit arguments.
            -- An argument can be either a type class constraint, or an annotated argument.
          | Data
            Position 
            String 
            [Exp] 
            [([String], Exp)]  
            [(Position, 
              String, 
              [Either ([String], Exp) Exp]
             )]
            -- ^ Data type declaration. [Exp] are the type class constraints,
            -- [([String], Exp)] are the annotated arguments for the type constructor.
            -- The last list is the list of constructors, the Left part is
            -- for a dependent quantification, the Right part is the usual arguments.  
          | SimpData
            Position {-Position for the type constructor-}
            String {- Type constructor name -}
            [String] {- Type constructor type arguments -}
            Exp {- residue kind -}
            [(Position, {- Position of the equation -}
              [Exp], {- arguments -}
              Position, {- Position of the constructor -}
              String, {- Constructor name-}
              [Exp] {- Constructor arguments-}
             )]
            -- ^ Simple data type declaration. [String] are the
            -- type arguments for the type constructor. Exp is a kind expression.
            -- The last list is the list of equations that defined the simple type.
          | ImportGlobal Position String
          | OperatorDecl Position String Int String
            -- ^ Declaration for fixity and priority of infix
            -- operator, e.g. infixr 30 $ . This means the infix operator $ is right associative
            -- and it has the lowest priority, which is 30. The lower the number is, the higher
            -- is the priority.
          | Class Position String [([String], Exp)] [(Position, String, Exp)]
          | Instance Position
            Exp
            [(Position, String, -- method name
              [String], -- arguments
              Exp) -- method definition
            ]
    
  deriving (Show)

-- | Command line instruction.
data Command =
  Eval Exp
  | Quit  
  | Help 
  | Type Exp
  | Load Bool String
  | Reload
  | Print Exp String
  | Display Exp
  | DisplayEx Exp -- ^ Displaying existential circuit.
  | Annotation Exp
  | ShowCirc
  deriving (Show)

type Program = [Decl] 

