module ConcreteSyntax where
import Utils
import Text.PrettyPrint
import Text.Parsec.Pos
import Data.List
import Prelude hiding((<>))


  
-- | Concrete syntax for the surface language.
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
  | LamAnn String Exp Exp
  | App Exp Exp
  | Pack Exp Exp
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

type Branches = [(String, [Exp], Exp)]

-- | Binding for let expression.
data Binding =
  BSingle (String, Exp)
  | BPair ([String], Exp)
  | BExist (String, String, Exp)
  | BPattern (String, [Exp], Exp)
  deriving (Show, Eq)


data Decl = 
  GateDecl Position String [Exp] Exp 
  | ControlDecl Position String [Exp] Exp 
  | Object Position String
  | Def Position String Exp [String] Exp
  | Data
    Position {-Position for the type constructor-}
    String {- Type constructor name -}
    [Exp] {- Type constraints -}
    [([String], Exp)]  {- args -}
    [(Position, {- Position for the constructor -}
      String, {- Constructor name -}
      [Either ([String], Exp) Exp] {- Constructor arguments:
                                  Left part is for a dependent quantification,
                                  Right part is for the usual type expression  -}
     )]
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
     )]  -- ^ Simple data type declaration.
  | ImportGlobal Position String
  | OperatorDecl Position String Int String -- ^ Declaration for fixity and priority of infix
    -- operator, e.g. infixr 30 $ . This means the infix operator $ is right associative
    -- and it has the lowest priority, which is 30. The lower the number is, the higher
    -- is the priority.
  | Class Position String [([String], Exp)] [(Position, String, Exp)]
  | Instance Position
    Exp
    [(Position, String, -- method name
      [String], 
      Exp) -- method definition
    ]
  | Defn Position String [Either Exp ([String], Exp)]
    [Either Exp ([String], Exp)] Exp -- ^ Infer mode function declaration.
    
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
  | GateCount Exp
  | DisplayEx Exp
  | ShowCirc
  | Annotation Exp
  deriving (Show)

type Program = [Decl] 

