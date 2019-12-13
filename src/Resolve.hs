module Resolve
       (
         ScopeError,
         Scope(..),
         Resolve(..),
         runResolve,
         emptyScope,
         resolve,
         toLScope,
         lookupScope,
         addConst,
         resolveDecl,
       )
       where

import Utils
import SyntacticOperations
import qualified ConcreteSyntax as C
import Syntax

import Prelude hiding ((.), (<>))

import Nominal
import Nominal.Atom
import Nominal.Atomic
import Control.Monad.Except
import Text.PrettyPrint
import Control.Monad.Identity
import qualified Data.Map as Map
import Data.Map (Map)
import Data.List

-- | A global scope that contains a map to tracks strings to known global names
-- (such as function and constructor names). 

data Scope = Scope {
  scopeMap :: Map String (Exp, Position)
  }

emptyScope :: Scope
emptyScope = Scope {
  scopeMap = Map.empty
  }

-- | Look up a string from the global scope. 
lookupScope :: Scope -> String -> Maybe (Exp, Position)
lookupScope scope x =
  case Map.lookup x (scopeMap scope) of
    Just a -> Just a
    Nothing -> Nothing


-- | A local scope that contains a global scope,
-- a map to track local string and variables.
data LScope = LScope {
  localScope :: Map String Variable,
  globalScope :: Scope
  }


-- | Construct a local scope from a global scope.
toLScope :: Scope -> LScope
toLScope scope = LScope {
  localScope = Map.empty,
  globalScope = scope
  }

-- | Add a variable name to a local scope.
addLScope :: LScope -> String -> Variable -> LScope
addLScope lscope x v = 
  let local = localScope lscope 
      local' = Map.insert x v local
      lscope' = lscope {localScope = local' }
  in lscope'
  

-- | Extend the local scope with a list of variable names.
lscopeVars :: LScope -> [String] -> (LScope -> [Variable] -> a) -> a
lscopeVars lscope ss body =
  freshNames ss $ \ as -> 
    let lscope' = foldr (\ (s , a) l -> addLScope l s a) lscope (zip ss as)
    in body lscope' as

-- | Lookup a string from local and global scope.
lookupLScope :: LScope -> String -> Maybe Exp
lookupLScope lscope x =
  case (Map.lookup x local, lookupScope global x) of
    (Just v, _) -> Just (Var v)
    (Nothing, Just a)-> Just (fst a)
    (Nothing, Nothing) -> Nothing
  where
    local = localScope lscope
    global = globalScope lscope


-- | Precise scope error information. Please see its Disp instance to see
-- the meaning of each error. 
data ScopeError = NotInScope String 
                 | ConstrErr Exp
                 | ScopePos Position ScopeError
                 | NoNest 
                 | MultiDef Position String Position
                 | LengthMismatch Int Int

instance Disp ScopeError where
  display flag (ScopePos p e) = display flag p $$ display flag e
  display flag (NotInScope s) =
    text "not in scope:" <+> text s
  display flag (ConstrErr a) =
    text "expecting a constructor."
  display flag (NoNest) =
    text "can't resolve nested pattern."
  display flag (MultiDef p x oldp) =
    display flag p <+> text "multiple definition:" <+> text x $$
    text "previously defined at:" <+> display flag oldp
  display flag (LengthMismatch n l) =
    text "arguments length mismatch:" $$
    text "expecting" <+> int l <+> text "non-uniform arguments" $$
    text "but get" <+> int n <+> text "non-uniform arguments"



-- | A monad for scope resolution.
type Resolve a = ExceptT ScopeError Identity a

-- | A run function for the R monad.
runResolve :: Resolve a -> Either ScopeError a
runResolve m = runIdentity $ runExceptT m

-- | Add a position to scope error if the error does not already
-- contain position information.
addScopePos :: Position -> ScopeError -> ScopeError 
addScopePos p a@(ScopePos _ _) = a
addScopePos p a = ScopePos p a

-- | Resolve concrete syntax to abstract syntax.
resolve :: LScope -> C.Exp -> Resolve Exp
resolve d (C.Pos p e) =
  do a <- resolve d e `catchError` \ e -> throwError $ addScopePos p e
     return $ Pos p a
    
resolve d (C.Var y) = 
  case lookupLScope d y of
   Nothing -> throwError $ NotInScope y
   Just x -> return x

resolve d (C.Base s) =
  let global = scopeMap (globalScope d) in
  case Map.lookup s global of
   Nothing -> throwError $ NotInScope s
   Just (x, _) -> return x

resolve d (C.Lam vs m) =
  lscopeVars d vs $ \d' xs -> 
  do m' <- resolve d' m
     if null xs then return m'
       else helper m' xs
  where helper (Lam bs) xs = 
          open bs $ \ ys m'' ->
          return (Lam ((xs++ys).m'')) 
        helper (Pos p e) xs =
          helper e xs >>= \ e' -> return $ Pos p e'
        helper a xs = return $ Lam (xs.a) 


resolve d (C.Forall ((vs, t):vars) m) =
  lscopeVars d vs $ \d' xs ->
  do m' <- resolve d' (C.Forall vars m)
     t' <- resolve d t
     case m' of
       Forall bd t'' | t'' == t' ->
         open bd $ \ ys b ->
         return $ (Forall ((xs++ys) . b) t')
       _ ->
         return $ Forall (xs . m') t'

resolve d (C.Forall [] m) = resolve d m

resolve d (C.App m n) = 
  do m' <- resolve d m
     n' <- resolve d n
     return (App m' n')

resolve d (C.Pair m n) = 
  do m' <- resolve d m
     n' <- resolve d n
     return (Pair m' n')

resolve d (C.Pack m n) = 
  do m' <- resolve d m
     n' <- resolve d n
     return (Pack m' n')

     
     
resolve d (C.Let [] m) = resolve d m

resolve d (C.Let ((C.BSingle (s, n)):defs) m) =
  lscopeVars d [s] $ \d' (x:[]) -> 
  do 
     n' <- resolve d n
     m' <- resolve d' (C.Let defs m)
     return (Let n' (x.m'))
     
resolve d (C.Let ((C.BPair (ss, m)):defs) n) = 
  lscopeVars d ss $ \d' xs -> 
    do m' <- resolve d m
       n' <- resolve d' (C.Let defs n)
       return (LetPair m' (abst xs n'))

resolve d (C.Let ((C.BExist (s, s', m)):defs) n) = 
  lscopeVars d [s, s'] $ \d' (x:y:[]) -> 
    do m' <- resolve d m
       n' <- resolve d' (C.Let defs n)
       return (LetEx m' ((x,y).n'))

resolve d (C.Let ((C.BPattern (c, vs, m)):defs) n) =
  do vs' <- mapM helper vs
     case lookupLScope d c of
       Nothing -> throwError $ NotInScope c
       Just (Const kid) ->
         lscopeVars d vs' $ \d' xs -> 
         do m' <- resolve d m
            n' <- resolve d' (C.Let defs n)
            return (LetPat m' (abst (PApp kid (map Right xs)) n'))
    where helper :: C.Exp -> Resolve String
          helper (C.Var x) = return x
          helper C.Wild = return "_"
          helper (C.Pos p x) = helper x
          helper a = throwError NoNest 

resolve d (C.Star) = return Star
resolve d (C.Box) = return Box 
resolve d (C.ExBox) = return ExBox
resolve d (C.UnBox) = return (UnBox)
resolve d (C.Revert) = return (Revert)
resolve d (C.RunCirc) = return (RunCirc)
     

resolve d (C.Case t br) = do
  t' <- resolve d t
  br' <- resolveBr d br
  return (Case t' br')
  where resolveBr :: LScope -> C.Branches -> Resolve Branches
        resolveBr d ((h, args, t):brs) = 
          case lookupLScope d h of 
            Nothing -> throwError $ NotInScope h
            Just (Const kid) ->
              do args' <- mapM helper args 
                 lscopeVars d args' $ \d' ys -> 
                   if null brs then
                     do t' <- resolve d' t
                        return $ B (((PApp kid (map Right ys)).t'):[])
                   else
                     do t' <- resolve d' t
                        B brs' <- resolveBr d brs
                        return $ B (((PApp kid (map Right ys)).t'):brs')
            Just a -> throwError $ ConstrErr a
        helper :: C.Exp -> Resolve String            
        helper (C.Var x) = return x
        helper C.Wild = return "_"
        helper (C.Pos p x) = helper x
        helper a = throwError NoNest 

resolve d (C.Arrow t u) = 
  do t' <- resolve d t
     u' <- resolve d u
     return (Arrow t' u')

resolve d (C.Imply t u) = 
  do ts <- mapM (resolve d) t
     u' <- resolve d u
     return (Imply ts u')

resolve d (C.Tensor t u) = 
  do t' <- resolve d t
     u' <- resolve d u
     return (Tensor t' u')
     
resolve d (C.Unit) = return Unit

resolve d (C.Bang t) = 
  do t' <- resolve d t
     return (Bang t')

resolve d (C.Circ t u) = 
  do t' <- resolve d t
     u' <- resolve d u
     return (Circ t' u')
     
resolve d (C.Pi vs t1 t2) =
  lscopeVars d vs $ \d' xs -> 
  do t1' <- resolve d t1
     t2' <- resolve d' t2
     return (Pi (abst xs t2') t1')

resolve d (C.Exists v t1 t2) =
  lscopeVars d [v] $ \d' (x:[]) -> 
  do t1' <- resolve d t1
     t2' <- resolve d' t2
     return (Exists (abst x t2') t1')

resolve d C.Set = return Set

-- | Add a constant to the scope.
addConst :: Position -> String -> (Id -> Exp) -> Scope -> Resolve (Id, Scope)
addConst p x f scope =
  case lookupScope scope x of
       Just (_, oldp) -> throwError $ MultiDef p x oldp
       Nothing ->
         let id = Id x
             exp = f id
             newMap = Map.insert x (exp, p) $ scopeMap scope
             scope' = scope{scopeMap = newMap}
         in return (id, scope')

-- | Resolve a concrete declaration into abstract declaration.
resolveDecl :: Scope -> C.Decl -> Resolve (Decl, Scope)
resolveDecl scope (C.GateDecl p gn params t) =
  do (id, scope') <- addConst p gn Const scope 
     let lscope' = toLScope scope'
     params' <- mapM (resolve lscope') params
     e <- resolve lscope' t
     return (GateDecl p id params' e, scope')

resolveDecl scope (C.ControlDecl p gn params t) =
  do (id, scope') <- addConst p gn Const scope 
     let lscope' = toLScope scope'
     params' <- mapM (resolve lscope') params
     e <- resolve lscope' t
     return (ControlDecl p id params' e, scope')

resolveDecl scope (C.Object p x) =
  do (id, scope') <- addConst p x LBase scope
     return (Object p id, scope')

resolveDecl scope (C.Def p f ty args def) =
  do (id, scope') <- addConst p f Const scope
     let lscope' = toLScope scope'
     ty' <- resolve lscope' ty
     lscopeVars lscope' args $ \ d xs ->
       do def' <- resolve d def
          let res = if null xs then def' else Lam (abst xs def') 
          return (Def p id ty' res, scope')

resolveDecl scope (C.Data p d vs constrs) =
  do (id, scope') <- addConst p d Base scope
     let tyArgs = map C.Var $ concat $ map (\ x ->
                                              case x of
                                                Left _ -> []
                                                Right (xs, ty) -> xs
                                           ) vs
         head = foldl C.App (C.Base d) tyArgs
         kd1 = foldr (\ v y ->
                        case v of
                          Right (x, ty) -> C.Pi x ty y
                          Left p -> y
                     ) C.Set vs
         lscope' = toLScope scope'
     kd <- resolve lscope' kd1
     let dKind = removeVacuousPi kd
     (constrs', scope'') <- resolveConstrs scope' head vs constrs
     return (Data p id dKind constrs', scope'')
       where resolveConstrs sc hd env [] = return ([], sc)
             resolveConstrs sc hd env ((p1, c1, cArgs1):cs) =
               do (c1', sc') <- addConst p1 c1 Const sc 
                  let lsc' = toLScope sc'
                  let ty = foldr (\ x z -> case x of
                                        Left (y, e) -> C.Pi y e z
                                        Right e -> C.Arrow e z
                                 ) hd cArgs1
                      t = foldr (\ x y -> case x of
                                            Left p -> C.Imply [p] y
                                            Right (xs, t) -> C.Forall [(xs, t)] y
                                ) ty vs
                  t' <- resolve lsc' t
                  (cs', sc'') <- resolveConstrs sc' hd env cs
                  return ((p1, c1', t'):cs' , sc'')

resolveDecl scope (C.Class pos c vs mths) =
    do (d, scope1) <- addConst pos c Base scope
       (dict, scope') <- addConst pos (c++"Dict") Const scope1
       let tyArgs = map C.Var $ concat $ map (\ x -> (fst x)) vs
           head = foldl C.App (C.Base c) tyArgs
           tys = map (\ (_, _, t) -> t) mths
           dictTy = C.Forall vs (foldr (\ x y -> C.Arrow (C.Bang x) y) head tys)
           kd1 = foldr (\ (x, ty) y -> C.Pi x ty y) C.Set vs
           lscope = toLScope scope'
       dictType <- resolve lscope dictTy    
       kd2 <- resolve lscope kd1
       let kd = removeVacuousPi kd2
       (mths', scope'') <- makeMethods scope' head vs mths
       return (Class pos d kd dict dictType mths', scope'')
         where makeMethods scope' head vs [] =
                 return ([], scope')
               makeMethods scope' head vs ((p, mname, mty):cs) =
                 do (d, scope'') <- addConst p mname Const scope'
                    let lscope' = toLScope scope''
                        ty = C.Bang $ C.Forall vs (C.Imply [head] mty)
                        ty1 = C.Bang $ C.Forall vs (C.Arrow head mty) 
                    ty' <- resolve lscope' ty
                    ty'' <- resolve lscope' ty1
                    (res, scope''') <- makeMethods scope'' head vs cs
                    return ((p, d, ty', ty''):res, scope''')

resolveDecl scope (C.Instance pos t mths) =
  do let lscope = toLScope scope
     t' <- resolve lscope t
     mths' <- makeMethods scope mths
     
     let (_, ty') = decomposeForall t'
         (_, h) = deCompose ty'
         Just (Right d', _) = getId h
         instName = "instAt" ++ hashPos pos ++ (getName d')
     (d, scope1) <- addConst pos instName Const scope    
     return (Instance pos d t' mths', scope1)
       where makeMethods scope [] = return []
             makeMethods scope ((p, mname, args, exp):cs) =
               do let lscope = toLScope scope
                  n <- resolve lscope (C.Base mname) `catchError`
                       \ e -> throwError $ ScopePos p e
                  let (Const id) = n
                  lscopeVars lscope args  $ \ d xs ->
                    do e' <- resolve d exp
                       let le = if null xs then e'
                             else Lam (abst xs e') 
                       res <- makeMethods scope cs
                       return ((p, id, le) :res)

resolveDecl scope (C.SimpData pos c args resKind eqs) =
  do (d, scope') <- addConst pos c LBase scope
     let lscope = toLScope scope'
     kd <- resolve lscope resKind
     let (bd, _) = deCompose (snd $ decomposePrefixes kd)
         lta = length bd
     (eqs', scope'') <- makeConstrs lta scope' eqs
     return (SimpData pos d (length args) kd eqs', scope'')
       where makeConstrs lta scope' [] = return ([], scope')
             makeConstrs lta scope' ((p1, tArgs, p2, cName, cArgs ):cs) =
               do (constr, scope'') <- addConst p2 cName Const scope'
                  let lscope = toLScope scope''
                      tArgs' = drop (length args) tArgs
                      mi = findIndex isPattern tArgs'
                      ty = foldr C.Arrow (foldl C.App (C.Base c) tArgs)
                           cArgs
                      args' = map (\ x -> ([x], C.Set)) args
                      vars = concat $ map getVars (drop (length args) tArgs)
                      ty' = if null vars then ty else C.Lam vars ty
                      ty'' = if null args then ty' else C.Forall args' ty'
                      lta' = length tArgs'
                  when (lta' /= lta) $ throwError $ ScopePos p1 (LengthMismatch lta' lta)
                  ty''' <- resolve lscope ty''
                  (res, scope''') <- makeConstrs lta scope'' cs
                  return ((p2, mi, constr, ty'''):res, scope''')
             isPattern :: C.Exp -> Bool
             isPattern (C.Pos p e) = isPattern e
             isPattern (C.App _ _) = True
             isPattern (C.Base _) = True
             isPattern _ = False
             getVars :: C.Exp -> [String]
             getVars (C.Pos p e) = getVars e
             getVars (C.Var x) = [x]
             getVars (C.App x y) = getVars x ++ getVars y
             getVars (C.Base _) = []
             
             
resolveDecl scope (C.ImportGlobal p f) = return (ImportDecl p f, scope)                  
resolveDecl scope (C.OperatorDecl p s i f) = return (OperatorDecl p s i f, scope)

