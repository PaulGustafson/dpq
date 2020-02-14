{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE PatternSynonyms, ViewPatterns #-}

-- | This module implements various of utility functions. 

module Utils where


import System.FilePath
import Text.Parsec.Pos
import Text.PrettyPrint
import Text.Parsec.Error(ParseError,showErrorMessages,errorPos,errorMessages)
import Prelude hiding((<>))
import Nominal
import Data.Char

-- | An empty data type for classifying variables. 
data V

instance AtomKind V where
  suggested_names _ = ["a", "b", "c", "d", "e", "x", "y", "z"]
  expand_names _ xs = xs ++ [ x ++ (show n) | n <- [1..], x <- xs ]

-- | A variable contain an atom for nominal representation and its name string for
-- error processing. 
data Variable = Variable (AtomOfKind V) (NoBind String) 
  deriving (Generic, Bindable, Nominal, NominalShow, NominalSupport, Ord)

instance NominalShow (NoBind String) where
  showsPrecSup sup d (NoBind x) = showsPrecSup sup d x

   
instance Show Variable where
  show (Variable a _) = show a

instance Eq Variable where
  (Variable x _) == (Variable y _) = x == y
  
instance Disp Variable where
  display True (Variable x (NoBind y)) = text y
  display False (Variable x _) = text (show x)
  
-- | An empty data type for labels.
data L
instance AtomKind L where
  suggested_names _ = ["l"]
  expand_names _ xs = xs ++ [ x ++ (show n) | n <- [1..], x <- xs ]

-- | Labels are used for representing the input/output of circuits. 
type Label = AtomOfKind L

instance Disp (AtomOfKind L) where
  display _ t = text (show t)

-- | A non-Unicode pattern definition for opening a binder.  
pattern Abst :: (Bindable a, Nominal t) => a -> t -> Bind a t
pattern Abst x t <- ((\ b -> open b (\ x b' -> (x, b'))) -> (x, t))

-- | Generate a list of fresh variables from a given list of strings.
freshNames :: [String] -> ([Variable] -> t) -> t
freshNames [] body = body []
freshNames (n:ns) body =
  freshName n $ \ a ->
  freshNames ns $ \ as ->
  body (a:as)
  where freshName s k =
          with_fresh $ \a -> k (Variable a (NoBind s))

-- | Generate a list of fresh labels from a given list of strings.
freshLabels :: [String] -> ([Label] -> t) -> t
freshLabels [] body = body []
freshLabels (n:ns) body =
  freshLabel n $ \ a ->
  freshLabels ns $ \ as ->
  body (a:as)
  where freshLabel s k =
          with_fresh $ \a -> k a

-- | Constant identifiers, they are used for top-level definitions and constructors.
data Id = Id String
        deriving (Show, Eq, Ord, Generic, NominalShow, NominalSupport, Nominal, Bindable)

-- | Get the name string from an identifier.
getName :: Id -> String
getName (Id s) = s

instance Disp Id where
  display _ (Id s) =
    if (isAlpha $ head s) then text s
    else parens (text s)

-- | Position information for error reporting. Build-in positions are
-- generated from the build-in type classes. 
data Position = P SourcePos | DummyPos | BuiltIn Int
  deriving (Show, Eq, NominalShow, NominalSupport, Generic, Nominal)

instance Nominal SourcePos where
  pi • p = p

instance NominalSupport SourcePos where
  support p = support ()
  
instance NominalShow SourcePos where
  showsPrecSup s d t a = ""


-- | Obtain a string that is unique to a position, this is
-- used to generate names for instance functions.
hashPos :: Position -> String
hashPos (P p) = (takeBaseName (sourceName p)) ++ (show $ sourceLine p)
hashPos (DummyPos) = "dummyPos"
hashPos (BuiltIn i) = "builtIn"++ show i

instance Disp Position where
  display b (P p) = display b p
  display _ (DummyPos) = text ""
  display _ (BuiltIn i) = text $ "BUILTIN#"++show i

class Disp a where
  display :: Bool -> a -> Doc

  dispRaw :: a -> Doc
  dispRaw = display False

  disp :: a -> Doc
  disp = display True
  
  precedence :: a -> Int
  precedence _ = 0

-- | Determine whether or not to put a parenthesis on an expression e.
-- If the current precedence level is higher than the precedence e, then
-- we put a parenthesis on e.   
dParen :: (Disp a) => Bool -> Int -> a -> Doc
dParen b level x =
   if level >= precedence x
   then parens $ display b  x 
   else display b x

instance Disp String where
  display _ x = text x

instance Disp SourcePos where
  display _ p =
    text (takeFileName $ sourceName p) <+> int (sourceLine p) <> text ":" 
    <> int (sourceColumn p) <> text ":"

instance Disp Doc where
  display _ = id

instance Disp ParseError where
  display b pe =
    display b (errorPos pe) $$
    (text "Parse Error:" <+> sem)
    where sem = text $ showErrorMessages "or" "unknown parse error"
                "expecting" "unexpected" "end of input"
                (errorMessages pe)

instance Disp a => Disp (Maybe a) where
  display _ Nothing = text ""
  display b (Just x) = display b x


-- * The zipper for counting

-- | A count data type that keeps track of the use of variables and global
-- identifiers, it also accounts for the case expressions. Due to
-- the case expression, Count is enssentially a tree. We will
-- couple Count with a list of history to form a zipper (ZipCount).
-- For more information about the zipper data type, please have a look at
-- Gerard Huet's paper: the zipper.

-- | In the context of linear type checking, the use of zipper for count
-- seems natural as we want to update count when type checking
-- a branch in the case expression, and we never revisit the branch after type checking.

data Count =
  Hole  -- ^ A placeholder that can be substituted with a Count.
  | Leaf Int -- ^ The inital count number without entering any case expression. 
  | C
    Id {-  The name of the data type that is being pattern matched on. -}
    Count {- The count before going into the case expression. -}
    [(Id, Count)] {- The count in each branch, Id is the name of the data constructor in the
                   pattern.-}
    -- ^ The node for the case expression. The first argument denotes the data type
    -- that is being pattern matched in the case expression. The second argument denotes
    -- the count before going into the case expression. The third argument denote the
    -- count in each branch of the case expression.
  deriving (Show, Eq, Nominal, Generic, NominalShow, NominalSupport, Ord)

-- | The count zipper, the left component is for the
-- current count (may be in a branch), the right component is
-- a stack of history(also called context).
type ZipCount = (Count, [Count]) 

-- | Initial count.
initCount :: ZipCount
initCount = (Leaf 0, [])

-- | Increment the current count in a count zipper, does not modify the context.
incr :: ZipCount -> ZipCount
incr (c, cxt) =
  let c' = mapC (+1) c in (c', cxt)
  where
    mapC f Hole = Hole
    mapC f (Leaf i) = Leaf (f i)
    mapC f (C id o ns) = C id o (map (\ (kid, c) -> (kid, mapC f c)) ns)

-- | Evaluate a count to a concrete number,
-- return Nothing if the count is not consistent due to branching, i.e.
-- a linear variables misused due to branching.
evalCount :: ZipCount -> Maybe Int
evalCount x = helper $ fst x 
  where helper Hole = Nothing
        helper (Leaf i) = Just i
        helper (C id _ ns) =
          let ns1 = map (\ (kid, c) -> (kid, helper c)) ns
          in case ns1 of
               [] -> Nothing
               (kid, Nothing):ns' -> Nothing
               (kid, Just c):ns' -> 
                 let fl = all (\ (_, c') -> c' == Just c) ns'
                 in if fl then Just c
                    else Nothing

-- | Prepare the count before entering the
-- case expression that match on a data type. 
enterCase :: ZipCount -> Id -> ZipCount
enterCase (c, cxt) id = (C id c [], cxt)

-- | Enter the subsequent case branch, must be used
-- right after 'enterCase'
nextCase :: ZipCount -> Id -> ZipCount
nextCase (C id o [], cxt) kid = 
  (o, (C id o ((kid, Hole):[])):cxt)
nextCase (c, (C id o ((kid, Hole):ns)):cxt) kid' =
  (o, (C id o ((kid', Hole):(kid, c):ns)):cxt)

-- | Exit the current case expression, must be used
-- after a sequence of 'nextCase'
exitCase :: ZipCount -> ZipCount
exitCase (c, (C id o ((kid, Hole):ns)):cxt) = (C id o ((kid, c):ns),cxt)

instance Disp Count where
   display _ Hole = text "@"
   display _ (Leaf n) = int n
   display flag (C id _ ns) =
     let childs = map (\ (kid, c) -> parens $ display flag kid <> comma <+> display flag c) ns
     in display flag id <+>
        braces (hsep childs)

instance Disp ZipCount where
  display flag (c, _) = display flag c
