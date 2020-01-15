{-#LANGUAGE FlexibleContexts#-}
module Parser
       ( ParserState,
         initialParserState,
         parseImports,
         parseModule,
         parseCommand,
         )
       where

import ConcreteSyntax
import Utils


import Prelude hiding (const)
import Text.Parsec.Indent
import Control.Monad.Identity
import Text.Parsec hiding (ParseError,Empty, State)
import Text.Parsec.Expr(Operator(..),Assoc(..),buildExpressionParser)
import Text.Parsec.Language
import qualified Text.Parsec.Token as Token
import qualified Text.Parsec as P
import qualified Data.IntMap as IM
import Data.Char
import Data.List

-- | A parser for DPQ is an ident-parser with a ParserState and input type
-- String.
type Parser a = IndentParser String ParserState a

-- | An expression parser state contains an expression parser together with
-- an operator table. The expression parser is build by combining 
-- operator table with the atomic expression parser. The operator table
-- can be updated during parsing when encountering an infix operator declaration,
-- in this case the expression parser will be rebuild as well.

data ParserState =
  ParserState {
    expParser :: IndentParser String ParserState Exp,
    expOpTable :: IM.IntMap [Operator String ParserState (IndentT Identity) Exp]
    }

initialParserState :: ParserState
initialParserState = ParserState{
  expParser = buildExpressionParser initialOpTable atomExp,
  expOpTable = IM.fromAscList (zip [0 ..] initialOpTable)
  }

-- | The precedence is in descending order (See Text.Parsec.Expr for
-- further information). Currently, we have the following build-in type operators:
-- !(precedence 5), *(precedence 7), -> (precedence 10).
initialOpTable = [[], [], [], [], [], [unaryOp "!" Bang], [], [binOp AssocLeft "*" Tensor] , [], [], [binOp AssocRight "->" Arrow], [], [], []]
  where binOp assoc op f = Infix (reservedOp op >> return f) assoc  
        unaryOp op f = Prefix (reservedOp op >> return f) 

        
-- | Parse a DPQ module from a file name 'srcName' and file
-- handler 'cnts', using the parser state 'st'.
parseModule :: String -> String -> ParserState -> Either P.ParseError ([Decl], ParserState)
parseModule srcName cnts st = 
  runIndent $ runParserT decls st srcName cnts

-- | Parse the import declarations from a file.
-- This is used to handle importation.
parseImports :: String -> String -> Either P.ParseError [Decl]
parseImports srcName cnts = 
  runIndent $ runParserT imports initialParserState srcName cnts
  where imports =
          do reserved "module"
             const
             reserved "where" 
             many importDecl

-- | Parse a command line string using a given parser state.
parseCommand :: String -> ParserState -> Either P.ParseError Command
parseCommand s st = runIndent $ runParserT command st "" s


---------------------------
-- *  A parser for command line
command :: Parser Command
command =
  do whiteSpace 
     quit <|>  help <|> typing <|>  reload <|>  load <|>  printing <|>
       displaying <|>  displayEx <|>  annotation <|> evaluation
     
-- showCirc =
--   do whiteSpace
--      reserved ":s"
--      eof
--      return ShowCirc

quit =
  do reserved ":q"
     eof
     return Quit

help =
  do reserved ":h"
     eof
     return Help

reload =
  do reserved ":r"
     eof
     return Reload

typing =
  do reserved ":t"
     t <- term
     eof
     return $ Type t

printing =
  do reserved ":p"
     t <- term
     path <- stringLiteral
     eof
     return $ Print t path

displaying =
  do reserved ":d"
     t <- term
     eof
     return $ Display t

displayEx =
  do reserved ":e"
     t <- term
     eof
     return $ DisplayEx t

annotation =
  do reserved ":a"
     t <- try varExp <|> parens opExp
     eof
     return $ Annotation t

load =
  do reserved ":l"
     path <- stringLiteral
     eof
     return $ Load True path

-- gateC =
--   do reserved ":g"
--      t <- term
--      eof
--      return $ GateCount t

evaluation =
  do t <- term
     eof
     return $ Eval t

-----------------------------
-- * Parsers for various of declarations
decls :: Parser ([Decl], ParserState)
decls = do
  reserved "module"
  name <- const
  reserved "where"
  bs <- block
        (simpleDecl <|> importDecl
        <|> classDecl <|> instanceDecl
        <|> controlDecl <|>  gateDecl <|>  objectDecl <|>  dataDecl
        <|> operatorDecl
        <|> try funDecl <|> funDef <?> "top level declaration") 
  st <- getState
  eof
  return (bs, st)
 
-- | A parser for operator fixity and priority. 
operatorDecl :: Parser Decl
operatorDecl = do
  r <- choice [reserved i >> return i | i <- ["infix","infixr","infixl"]]
  level <- fromInteger <$> integer
  op <- operator
  p <- getPosition
  st <- getState
  let table' = IM.insertWith (++) level [toOp op r App Base] $ expOpTable st
      prog' = buildExpressionParser (map snd (IM.toAscList table')) atomExp
  putState $ ParserState prog' table' 
  return (OperatorDecl (P p) op level r)
  where toOp op "infix" app var =
          Infix (reservedOp op >> return (\ x y -> app (app (var op) x) y)) AssocNone
        toOp op "infixr" app var =
          Infix (reservedOp op >> return (\ x y -> app (app (var op) x) y)) AssocRight
        toOp op "infixl" app var =
          Infix (reservedOp op >> return (\ x y -> app (app (var op) x) y)) AssocLeft

-- | A parser for import declaration.
importDecl :: Parser Decl
importDecl = impGlobal
  where impGlobal = 
          do reserved "import"
             p <- getPosition
             mod <- stringLiteral
             return $ ImportGlobal (P p) mod              

-- | A parser for class declaration. We allow phatom class, i.e. class without
-- any method, in that case, one should not use the keyword "where".              
classDecl :: Parser Decl
classDecl =
  do reserved "class"
     (p, c, vs) <- manyLines
                   (do{p <- getPosition;
                       c <- const;
                       return $ \ ps -> (p, c, ps)}) (try ann <|> impAnn)
     mds <- option [] $ do{reserved "where";
                           block method}
     return $ Class (P p) c vs mds
       where method =
               do pos <- getPosition
                  n <- parens operator <|> var
                  reservedOp "::"
                  t <- typeExp
                  return (P pos, n, t)

-- | A parser for instance declaration. For the instance of the phantom class,
-- one should not use the keyword "where".                  
instanceDecl :: Parser Decl
instanceDecl =
  do reserved "instance"
     p <- getPosition
     t <- instanceType
     mds <- option [] $ do{reserved "where";
                           block method}
     return $ Instance (P p) t mds
       where method =
               do pos <- getPosition
                  n <- parens operator <|> var
                  args <- many var
                  reservedOp "="
                  def <- term
                  return (P pos, n, args, def)

-- | A parser for object declaration.
objectDecl :: Parser Decl
objectDecl =
  do reserved "object"
     p <- getPosition     
     o <- const
     return $ Object (P p) o

-- | A parser for gate declaration
gateDecl :: Parser Decl
gateDecl =
  do reserved "gate"
     p <- getPosition
     g <- const
     args <- many (const >>= \ a -> return $ Pos (P p) (Base a))
     reservedOp "::"
     ty <- typeExp
     return $ GateDecl (P p) g args ty

-- | Generalized controlled declaration. 

controlDecl =
  do reserved "controlled"
     p <- getPosition
     g <- const
     args <- many (const >>= \ a -> return $ Pos (P p) (Base a))
     reservedOp "::"
     ty <- typeExp
     return $ ControlDecl (P p) g args ty

-- | A parser for data type declaration. We allow data type without any constructor,
-- in that case, one should not use '='.     
dataDecl :: Parser Decl
dataDecl = 
  do reserved "data"
     tc <- option [] $ do{
             tyClass <- parens (sepBy1 typeExp comma);
             reserved "=>";
             return tyClass
             }
     (p, head, vs) <- manyLines
                      (do{p <- getPosition;
                          c <- const;
                          return $ \ ps -> (p, c, ps)})
                      annotation
     constrs <- option [] $
                reservedOp "=" >>
                (sepBy1 br (reservedOp "|"))
     return $ Data (P p) head tc vs constrs
     where br = manyLines (do{p <- getPosition;
                              c <- const;
                              return $ \ ps -> (P p, c, ps)}) arg
           arg = try (singleExp >>= \ x -> return $ Right x) <|>
                     (ann >>= \ x -> return $ Left x)
           -- prefix = try annotation <|> classExp
           annotation = try ann <|> impAnn
             -- do x <- 
             --    return $ x
           --classExp = parens typeExp -- >>= \ x -> return $ Left x
             
-- | A parser for simple data type declaration.                
simpleDecl :: Parser Decl
simpleDecl = 
  do reserved "simple"
     p <- getPosition
     head <- const
     vs <- many var
     reservedOp "::"
     kd <- kindExp
     reserved "where"
     constrs <- block (br head)
     when (null constrs) $ unexpected ("expected at least one constructor for simple type.")
     return $ SimpData (P p) head vs kd constrs
     where br h =
             do pPat <- getPosition
                c <- const
                when (h /= c)
                  $ unexpected (c++", expected name: "++ h)
                args <- many singlePat
                reservedOp "="
                manyLines (do{p <- getPosition;
                              cons <- const;
                              return $ \ tys -> (P pPat, args, P p, cons, tys)}) 
                  singlePat

 
-- | A parser for function declaration.                     
funDecl :: Parser Decl
funDecl =
  do (f, ty) <- try $ do{ 
       f <- parens operator <|> var;
       reservedOp "::";
       ty <- typeExp;
       return (f, ty);
       }
     p <- getPosition                  
     f' <- try var <|> parens operator
     when (f /= f')
       $ unexpected (f'++", expected name: "++ f)
     args <- many var
     reservedOp "="
     def <- term
     return $ Def (P p) f ty args def

-- | Function definition in the infer mode.
funDef :: Parser Decl
funDef =
  do p <- getPosition 
     f <- parens operator <|> var
     qs <- option [] $ try $ 
             do ans <- many1 (try annotation <|> classExp)
                reservedOp "."
                return ans
     args <- if null qs then many (try explicitAnnotation <|> classExp)
             else many1 (try explicitAnnotation <|> classExp)
     reservedOp "="
     def <- term
     return $ Defn (P p) f qs args def
       where explicitAnnotation =
               do x <- ann
                  return $ Right x
             annotation =
               do x <- ann <|> impAnn
                  return $ Right x
             classExp = parens typeExp >>= \ x -> return $ Left x



-- | A parser for term, built from the operator table.
term = wrapPos $ getState >>= \st -> expParser st

-- | 'kindExp' is a synonym for 'term'. 
kindExp = term

-- | 'typeExp' is a synonym for 'term'.
typeExp = term

--------------------------------
-- * Parsers for various atomic expressions

-- | An atomic expression parser, of course it is defined mutually recursively
-- with the full expression parser. 
atomExp :: Parser Exp
atomExp = wrapPos (
         circType
       <|> forallType
       <|> ifExp
       <|> caseExp
       <|> letExp
       <|> doExp
       <|> existsType
       <|> lamAnn
       <|> lam
       <|> idiomExp
       <|> nat
       <|> vector
       <|> implicitType
       <|> existsExp
       <|> withAnn
       <|> piType
       <|> impType
       <|> appExp
       <?> "expression")

-- | A function for constructing a parser that parse h and many p, they can be across many lines,
-- but they must be properly indented. 

manyLines h p = withPos $ h <*/> p

withAnn =
  do reserved "withType"
     ty <- typeExp
     reservedOp ":"
     t <- term
     return $ WithAnn t ty

-- | An expression parser for pattern application. 
patApp :: Parser Exp
patApp =
  wrapPos $ manyLines (do{head <- constExp ; 
                          return $ foldl' (\ z x -> App z x) head}) singlePat

-- | An expression parser for a single pattern.
singlePat = wrapPos (try varExp <|> try constExp <|> parens patApp <?> "single pattern")

-- | An expression parser for a single expression.
singleExp = wrapPos (try varExp <|> try constExp <|> parens term <?> "single expression")

-- | A parser for annotation. e.g. (x1 x2 :: Nat).
ann = parens $ 
      do xs <- many1 var
         reservedOp "::"
         ty <- typeExp 
         return (xs, ty)    

-- | Implicit annotation, e.g. in Eq a, a implicitly means (a :: Type).
impAnn = var >>= \ x -> return ([x], Set)

-- | A parser for operator.
opExp =
  do op <- operator
     return $ Base op

-- | Parse m, then parse p, but return the
-- result of m.
followedBy m p =
  do r <- m
     p
     return r

nat =
  do i <- naturals
     return $ toNat i
     where toNat i | i == 0 = Base "Z"
           toNat i | otherwise = App (Base "S") $ toNat (i-1)
-- | A parser for the vector bracket notation.
vector =
  do elems <- brackets $
              (term `sepBy` comma)
     return $ foldr (\ x y -> App (App (Base "VCons") x) y) (Base "VNil") elems

-- | A parser for if-then-else expression.
ifExp =
  do reserved "if"
     c <- term
     reserved "then"
     t1 <- term
     reserved "else"
     t2 <- term
     return $ Case c [("True", [], t1), ("False", [], t2)]

-- | A parser for Pi-type.     
piType =
  do (vs, ty) <- try $ followedBy (parens $
                                    do vs <- many1 var
                                       reservedOp "::"
                                       ty <- typeExp
                                       return (vs, ty))
                           (reservedOp "->") 
     t <- typeExp
     return $ Pi vs ty t

implicitType =
  do (vs, ty) <- try $ followedBy (braces $
                                    do vs <- many1 var
                                       reservedOp "::"
                                       ty <- typeExp
                                       return (vs, ty))
                           (reservedOp "->") 
     t <- typeExp
     return $ PiImp vs ty t

-- | A parser for existential type. 
existsType =
 do reserved "exists"
    v <- var
    reservedOp "::"
    ty <- typeExp
    reservedOp "."
    t <- typeExp
    return $ Exists v ty t

instanceType =
  do r <- option [] (do {reserved "forall";
                         vs <- many1 ((ann >>= \ x -> return x) <|>
                                      (impAnn >>= \ x -> return x));
                         reservedOp ".";
                         return vs})
     t <- try impType <|> appExp 
     return $ makeType r t
  where makeType [] t = t
        makeType ((xs, ty) : res) t =
          let t' = makeType res t in Forall [(xs, ty)] t'

        
impType = do
  constraints <- try $ do constraints <- parens $ typeExp `sepBy` comma
                          reservedOp "=>"
                          return constraints
  ty <- typeExp
  return $ Imply constraints ty

forallType =
 do vs <- try $ do reserved "forall"
                   vs <- many1 (try ann <|> impAnn)
                   reservedOp "."
                   return vs
    t <- typeExp
    return $ Forall vs t

circType =
  do reserved "Circ"
     (t, u) <- parens $ do
                t <- typeExp
                comma
                u <- typeExp
                return (t, u)
     return $ Circ t u

set = reserved "Type" >> return Set

unit = reservedOp "()" >> return Star

unitTy = reserved "Unit" >> return Unit

lamAnn = do
  v <-  try $
        do reservedOp "\\"
           v <- var
           reservedOp "::"
           return v
  ty <- typeExp
  reservedOp "."
  t <- term
  return $ LamAnn v ty t
     
lam =
 do reservedOp "\\"
    vs <- many1 var
    reservedOp "."
    t <- term
    return $ Lam vs t

pairExp = parens $
          do t1 <- term
             comma
             t2 <- term
             return $ Pair t1 t2

existsExp = braces $
          do t1 <- term
             comma
             t2 <- term
             return $ Pack t1 t2 
  
caseExp =
  withPos $
  do reserved "case"
     e <- term
     reserved "of"
     indented
     brs <- block branch
     return $ Case e brs
  where branch = withPos $
           do h <- const
              args <- many (try varExp <|> wild)
              reservedOp "->"
              indented
              b <- term
              return (h, args, b)

boxExp :: Parser Exp
boxExp = reserved "box" >> return Box 

exBoxExp :: Parser Exp     
exBoxExp = reserved "existsBox" >> return ExBox 

unBoxExp = reserved "unbox" >> return UnBox 

revertExp = reserved "revert" >> return Revert

runCircExp = reserved "runCirc" >> return RunCirc


letExp = handleLet True

letStatement = handleLet False

-- | A parser to handle let expression and let statement.
handleLet b =
  if b then
    do reserved "let"
       bds <- block bind
       reserved "in"
       t <- term
       return $ Let bds t
  else
    do reserved "let"
       bds <- block bind
       notFollowedBy $ reserved "in"
       return $ Let bds Unit
  where bind = letPattern <|> pair <|> existential <|> single
        pair =
          do xs <- parens $ 
                       do x <- try var <|> wildString
                          comma
                          xs <- sepBy1 (try var <|> wildString) comma
                          return (x:xs)
             reservedOp "="
             d <- term
             return $ BPair (xs, d)
        existential =
          do (x, y) <- braces $
                       do x <- try var <|> wildString
                          comma
                          y <- try var <|> wildString
                          return $ (x, y)
             reservedOp "="
             d <- term
             return $ BExist (x, y, d)             
        single =
          do n <- try var <|> wildString
             reservedOp "="
             d <- term
             return $ BSingle (n, d)
        letPattern =
          do c <- try const
             ps <- many (try varExp <|> wild)
             reservedOp "="
             t <- term
             return $ BPattern (c, ps, t)

-- | A parser for application.
appExp =
   manyLines (do{head <- headExp;
                 pos <- getPosition;
                 return $ foldl (\ z x -> Pos (P pos) $ App z x) head}) arg
  where headExp = wrapPos $ try unit <|> try opExp <|> unitTy <|> set <|> boxExp <|> exBoxExp
                  <|> unBoxExp <|> revertExp <|> runCircExp
                  <|> try varExp <|> try constExp <|>
                  do{
                     tms <- parens (term `sepBy1` comma);
                     return $ foldl (\ x y -> Pair x y) (head tms) (tail tms)
                     }
                            
        arg = wrapPos $ try unit <|> unitTy <|> set
              <|> try varExp <|> try constExp <|> existsExp <|> nat <|> try vector <|> idiomExp
              <|> do{
                     tms <- parens (term `sepBy1` comma);
                     return $ foldl (\ x y -> Pair x y) (head tms) (tail tms)
                     }
                  
varExp = (var >>= \ x -> return $ Var x) 

wild = reservedOp "_" >> return Wild

wildString = reservedOp "_" >> return "_"

constExp = const >>= \ x -> return $ Base x

var =
  do n <- identifier
     if (isUpper (head n)) then
       unexpected $ "uppercase word: "++n++", expected to begin with lowercase letter"
       else return n

const = 
  do n <- identifier  
     if (isLower (head n)) then
       unexpected $ "lowercase word: "++ n ++", expected to begin with uppercase letter"
       else return n

wrapPos :: Parser Exp -> Parser Exp
wrapPos par =
  do q <- getPosition
     e <- par
     let e' = pos (P q) e
     return e'
  where pos x (Pos y e) | x==y = Pos y e
        pos x y = Pos x y

-- | Parsing the inside of an idiom braket.
applicativeExp =
   manyLines (do{head <- wrapPos $ try varExp <|> try constExp <|> parens term <|> idiomExp;
                return $ foldl' (\ z x -> App (App (Var "ap") z) x)
                (App (Var "pure") head)}) (wrapPos $ arg)
  where arg = try varExp <|> try constExp <|> parens term <|> idiomExp
              

-- | A parser for idiom braket, it adds a ''join'' at the applicativeExp.
idiomExp :: Parser Exp
idiomExp = do try $ reservedOp "[|"
              t <- applicativeExp
              reservedOp "|]"
              return (App (Var "join") t)

data DoBinding = LetStmt [Binding] | PatternBind (Binding, Exp) | Stmt Exp                

-- | A parser for do expression. We allow direct pattern matching when using '<-',
-- such pattern matching is translated to let pattern matching. We also allow
-- let statement.
doExp :: Parser Exp
doExp =
  do reserved "do"
     bds <- block pseudoDecl
     desugar 0 bds 
       where pseudoDecl = bd <|> try letStmts <|> stmt
             pat = do c <- const
                      ps <- many (try varExp <|> wild)
                      return $ BPattern (c, ps, Wild)
             exists =
                braces $
                do x <- try var <|> wildString
                   comma
                   y <- try var <|> wildString
                   return $ BExist (x, y, Wild)
             leftPair =
                parens $
                do x <- try var <|> wildString
                   comma
                   xs <- sepBy1 (try var <|> wildString) comma
                   return $ BPair (x:xs, Wild)
             leftVar =
               do v <- try var <|> wildString
                  return $ BSingle (v, Wild)
             makeBind v (BSingle (x, _)) = BSingle (x, v)
             makeBind v (BPair (xs, _)) = BPair (xs, v)
             makeBind v (BExist (x,y, _)) = BExist (x, y, v)
             makeBind v (BPattern (x,y, _)) = BPattern (x, y, v)
             
             binding = try leftVar <|> leftPair <|> exists <|> pat  
             bd = do
               x <- try $
                    do{x <- binding;
                       reservedOp "<-";
                       return x}
               t <- term
               return $ PatternBind (x, t)
             stmt =
               do t <- term
                  return $ Stmt t
             letStmts =
               do (Let bds _) <- letStatement
                  return $ LetStmt bds
               
             desugar n (Stmt t:[]) =
               return t 
             desugar n (PatternBind _ : []) =
               unexpected $ "a do block should end with a non-binding expression."
             desugar n (LetStmt _ : []) =
               unexpected $ "a do block should end with a non-binding expression."
             desugar n (Stmt t : xs) =
               do t' <- desugar n xs
                  return $ App (App (Var "seq") t) t'
             desugar n (LetStmt bds : xs) =
               do t' <- desugar n xs
                  return $ Let bds t'
             desugar n (PatternBind (x, t):xs) =
               do t' <- desugar (n+1) xs
                  let v = "#bindVar"++ show n 
                  return $ App (App (Var "bind") t) (Lam [v] (Let [makeBind (Var v) x] t'))
             
               
-- * Lexer

dpqStyle :: (Stream s m Char, Monad m) => Token.GenLanguageDef s u m
dpqStyle = Token.LanguageDef
                { Token.commentStart   = "{-"
                , Token.commentEnd     = "-}"
                , Token.commentLine    = "--"
                , Token.nestedComments = True
                , Token.identStart     = letter
                , Token.identLetter    = alphaNum <|> oneOf "_'"
                , Token.opStart        = oneOf ":!#$%&*+./<=>;?@\\^|-`"
                , Token.opLetter       = oneOf ":!#$%&*+./<=>;?@\\^|-`"
                , Token.caseSensitive  = True
                , Token.reservedNames =
                  [
                    "gate", "in", "let", "controlled",
                    "case", "of", "exists", "implicitly",
                    "data", "import", "class", "instance",
                    "simple", "withType", "revert", "box", "unbox", "existsBox",
                    "runCirc",
                    "object", "Circ", "Unit", "do",
                    "where", "module", "infix","infixr", "infixl",
                    "Type", "forall", "if", "then", "else",
                    "pi", "sin", "cos",  "exp", "log", "log", "sqrt",
                    "plusReal", "minusReal", "cast",  "divReal", "mulReal", "eqReal", "ltReal",
                    "round"
                  ]
               , Token.reservedOpNames =
                    [ ".", "\\", "<-", "->", "::",  "*", "()", "!", "_", ":", "=", "=>"]
                }


tokenizer :: (Stream s m Char, Monad m) => Token.GenTokenParser s u m
tokenizer = Token.makeTokenParser dpqStyle

stringLiteral :: (Stream s m Char, Monad m) => ParsecT s u m String
stringLiteral = Token.stringLiteral tokenizer

identifier :: (Stream s m Char, Monad m) => ParsecT s u m String
identifier = Token.identifier tokenizer

whiteSpace :: (Stream s m Char, Monad m) => ParsecT s u m ()
whiteSpace = Token.whiteSpace tokenizer

reserved :: (Stream s m Char, Monad m) => String -> ParsecT s u m ()
reserved = Token.reserved tokenizer

reservedOp :: (Stream s m Char, Monad m) => String -> ParsecT s u m ()
reservedOp = Token.reservedOp tokenizer

operator :: (Stream s m Char, Monad m) => ParsecT s u m String
operator = Token.operator tokenizer

colon :: (Stream s m Char, Monad m) => ParsecT s u m String
colon = Token.colon tokenizer

integer :: (Stream s m Char, Monad m) => ParsecT s u m Integer
integer = Token.integer tokenizer

naturals :: (Stream s m Char, Monad m) => ParsecT s u m Integer
naturals = Token.natural tokenizer

brackets :: (Stream s m Char, Monad m) => ParsecT s u m a -> ParsecT s u m a
brackets = Token.brackets tokenizer

parens :: (Stream s m Char, Monad m) => ParsecT s u m a -> ParsecT s u m a
parens  = Token.parens tokenizer

angles :: (Stream s m Char, Monad m) => ParsecT s u m a -> ParsecT s u m a
angles  = Token.angles tokenizer

braces :: (Stream s m Char, Monad m) => ParsecT s u m a -> ParsecT s u m a
braces = Token.braces tokenizer

dot :: (Stream s m Char, Monad m) => ParsecT s u m String
dot = Token.dot tokenizer

lexeme :: (Stream s m Char, Monad m) => ParsecT s u m a -> ParsecT s u m a
lexeme = Token.lexeme tokenizer

comma :: (Stream s m Char, Monad m) => ParsecT s u m String
comma = Token.comma tokenizer
