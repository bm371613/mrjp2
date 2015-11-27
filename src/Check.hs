module Check (checkProgramReturningGlobals) where

import Control.Monad (foldM, unless, when)
import Control.Monad.Except (
    catchError, Except, MonadError, runExcept, throwError)
import Control.Monad.State (MonadState, StateT, evalStateT, get, put, state)
import Data.Foldable (Foldable, find)
import qualified Data.Foldable (elem)
import Data.List (nub, partition)
import Data.Map (empty, fromList, insert, Map, member, (!))
import qualified Data.Map (lookup)
import GHC.Exts (sortWith)
import Text.Printf (printf)

import Parser.AbsLatte
import Types

-- check monad

type Scope = Map String Type

data Context =
      NoContext
    | FunctionContext
    { ctxFun :: FunSig
    , ctxScopes :: [Scope]
    }
    | MethodContext
    { ctxCls :: ClsSig
    , ctxFun :: FunSig
    , ctxScopes :: [Scope]
    } deriving (Show)

setScopes scopes (FunctionContext f _) = FunctionContext f scopes
setScopes scopes (MethodContext c f _) = MethodContext c f scopes

data CheckState = CheckState
    { globals :: Globals
    , context :: Context
    } deriving (Show)
emptyCheckState = CheckState (Globals empty empty) NoContext

newtype Check a
    = Check (StateT CheckState (Except String) a)
   deriving (Monad, MonadState CheckState, MonadError String)

runCheckMonad :: Check a -> CheckState -> Either String a
runCheckMonad (Check check) state = runExcept $ evalStateT check state

checkProgramReturningGlobals :: Program -> Either String Globals
checkProgramReturningGlobals program = runCheckMonad m emptyCheckState
    where
    m = do
        check program
        s <- get
        return $ globals s

-- helpers

ensureUnique :: [PIdent] -> Check ()
ensureUnique = ensureUniqueOnSorted . sortWith name
    where
    ensureUniqueOnSorted [] = return ()
    ensureUniqueOnSorted (_:[]) = return ()
    ensureUniqueOnSorted (first : second : rest) =
        if name first == name second
        then throwError $ printf
                "Conflicting definitions of %s in lines %d, %d"
                (name first) (lineNo first) (lineNo second)
        else ensureUniqueOnSorted (second : rest)

withContext :: Context -> Check a -> Check a
withContext c m = do
    CheckState globals oldContext <- get
    put $ CheckState globals c
    result <- m
    put $ CheckState globals oldContext
    return result

withPushedScope :: Scope -> Check a -> Check a
withPushedScope s m = do
    CheckState globals c <- get
    let scopes = ctxScopes c
    put $ CheckState globals (setScopes (s:scopes) c)
    result <- m
    put $ CheckState globals c
    return result
    where

define :: PIdent -> Type -> Check ()
define ident t = do
    CheckState globals c <- get
    let (scope:scopes) = ctxScopes c
    let n = name ident
    when (member n scope) $ throwError $ printf
        "%s is already defined in this scope" n
    let newScope = insert n t scope
    put $ CheckState globals (setScopes (newScope:scopes) c)
    return ()

ensureAssignable :: Type -> Type -> Check ()
ensureAssignable lhs rhs = do
    ok <- case (lhs, rhs) of
            (TObj lId, TObj rId) -> do
                CheckState globals _ <- get
                return $ elem (name lId)
                    $ superNames $ classes globals ! name rId
            (TObj _, BaseObject) -> return True
            otherwise -> return $ lhs == rhs
    unless ok $ throwError "Type mismatch"

located :: Positioned p => p -> Check a -> Check a
located p m = catchError m $
    \e -> throwError $ printf "%s (line %d)" e (lineNo p)

-- checkable

class Checkable a t | a -> t where
    check :: a -> Check t

instance Checkable Program () where
    check (Program topDefs) = do
        -- ensure builtinss are not redefined
        let builtinNames = map fst builtins
        mapM_ ((\id -> when (name id `elem` builtinNames) $ throwError $ printf
                "%s is a built-in (line %d)" (name id) (lineNo id)
            ) . pIdent ) topDefs
        -- ensure top defs have unique identifiers
        ensureUnique $ map pIdent topDefs
        -- put signatures of functions and classes to state
        topoClsOrder <- checkClsExtTree clsDefs clsExtDefs
        clsSigMap <- foldM addClsSig empty topoClsOrder
        let globals = Globals clsSigMap  (fromList $ builtins ++
                [(name fd, makeFunSig fd) | GlFunDef fd <- funDefs])
        unless (Data.Map.lookup "main" (functions globals)
                == Just (FunSig (TPrim Int) []))
            $ throwError "No definition of global function: int main()"
        state (\s -> ((), CheckState globals (context s)))
        -- check each function and class
        mapM_ check topDefs
        return ()
        where
        builtins = [
            ("printInt", FunSig Void [TPrim Int]),
            ("printString", FunSig Void [TPrim Str]),
            ("error", FunSig Void []),
            ("readInt", FunSig (TPrim Int) []),
            ("readString", FunSig (TPrim Str) [])]
        isFunDef (GlFunDef _) = True
        isFunDef _ = False
        hasSuper (ClsExtDef {}) = True
        hasSuper _ = False
        (funDefs, nonFunDefs) = partition isFunDef topDefs
        (clsExtDefs, clsDefs) = partition hasSuper nonFunDefs

        checkClsExtTree :: [TopDef] -> [TopDef] -> Check [TopDef]
        checkClsExtTree checked [] = return checked
        checkClsExtTree [] (c : _) = throwError $ printf
                "Cannot resolve class inheritance (line %d)"
                (lineNo $ pIdent c)
        checkClsExtTree (currentCls : checkedClss) unchecked = do
            let (ok, rest) = partition
                    (\c -> name (super c) == name currentCls)
                    unchecked
            tail <- checkClsExtTree (ok ++ checkedClss) rest
            return $ currentCls : tail

        makeClsSigItem :: ClsDefItem -> ClsSigItem
        makeClsSigItem (AttrDef t pIdent _) = Attr (name pIdent) t
        makeClsSigItem (MethDef funDef) = Method (name funDef)
                (makeFunSig funDef)

        mergeClsSigItems :: [ClsSigItem] -> [ClsSigItem] -> Check [ClsSigItem]
        mergeClsSigItems mergedItems [] = return mergedItems
        mergeClsSigItems mergedItems (clsItem : leftItems) =
            let found = find (\i -> name i == name clsItem) mergedItems
            in case (clsItem, found) of
                (_, Nothing) ->
                    mergeClsSigItems (mergedItems ++ [clsItem]) leftItems
                (Method _ s1, Just (Method _ s2)) | s1 == s2 ->
                    mergeClsSigItems mergedItems leftItems
                otherwise -> throwError $ printf
                    "Illegal redefinition of %s" (name clsItem)

        addClsSig :: Map String ClsSig -> TopDef -> Check (Map String ClsSig)
        addClsSig sigs (ClsDef clsIdent items) = return $ insert
                (name clsIdent)
                (ClsSig [name clsIdent] (map makeClsSigItem items)) sigs
        addClsSig sigs (ClsExtDef clsIdent superIdent items) = do
            let superSig = sigs ! name superIdent
            let newSigItems = map makeClsSigItem items
            sigItems <- catchError
                (mergeClsSigItems (clsItems superSig) newSigItems)
                (\e -> throwError $ printf "%s\n\tin class %s (line %d)"
                    e (name clsIdent) (lineNo clsIdent))
            return $ insert (name clsIdent)
                (ClsSig (name clsIdent:superNames superSig) sigItems) sigs

instance Checkable Type () where
    check Void = return ()
    check (TPrim p) = return ()
    check (TObj pIdent) = let clsName = name pIdent in do
        s <- get
        unless (member clsName $ classes $ globals s) $ throwError $ printf
            "Undefined: %s" clsName
    check (TPrimArr p) = return ()
    check (TObjArr clsIdent) = check (TObj clsIdent)

instance Checkable TopDef () where
    check (GlFunDef funDef) = do
        s <- get
        let funSig = functions (globals s) ! name funDef
        withContext (FunctionContext funSig []) $ check funDef
    check clsDef = do
        ensureUnique $ map pIdent $ items clsDef
        mapM_ checkItem $ items clsDef
        return ()
        where
        checkItem (AttrDef t ident _) = located ident $ check t
        checkItem (MethDef funDef) = do
            s <- get
            let clsSig = classes (globals s) ! name clsDef
            withContext (MethodContext clsSig (makeFunSig funDef) [])
                $ check funDef

instance Checkable FunDef () where
    check funDef = do
        ensureUnique $ map pIdent (funArgs funDef)
        located funDef $ do
                check $ returnType funDef
                mapM_ (check . argType) (funArgs funDef)
        let argsScope = fromList [(name id, t) | Arg t id <- funArgs funDef]
        withPushedScope argsScope $ check $ body funDef
        let (Block stmts) = body funDef
        unless (returnType funDef == Void) $
            unless (any terminating stmts) $ throwError $ printf
                "Missing return statement in %s (line %d)"
                (name funDef) (lineNo funDef)
        return ()
        where
        terminating (Ret _ _) = True
        terminating (VRet _) = True
        terminating (BStmt (Block stmts)) = any terminating stmts
        terminating (If _ ELitTrue s) = terminating s
        terminating (IfElse _ ELitTrue s _) = terminating s
        terminating (IfElse _ ELitFalse _ s) = terminating s
        terminating (IfElse _ _ s1 s2) = terminating s1 && terminating s2
        terminating (While _ ELitTrue s) = True
        terminating (SExp (ECall ident []) _) = name ident == "error"
        terminating _ = False

instance Checkable Block () where
    check (Block stmts) = withPushedScope empty $ mapM_ check stmts

instance Checkable Stmt () where
    check (Empty _) = return ()
    check (BStmt block) = check block
    check (Decl t items semiC) = located semiC $ do
        check t
        sequence_ [do
            case i of
                Init _ e -> do
                    et <- check e
                    ensureAssignable t et
                NoInit _ -> return ()
            define (pIdent i) t
            | i <- items]
    check (Ass lv e semiC) = located semiC $ do
        lt <- check lv
        et <- check e
        ensureAssignable lt et
    check (Incr lv semiC) = located semiC $ do
        lt <- check lv
        unless (lt == TPrim Int) $ throwError "Type mismatch in incrementation"
    check (Decr lv semiC) = located semiC $ do
        lt <- check lv
        unless (lt == TPrim Int) $ throwError "Type mismatch in decrementation"
    check (Ret e semiC) = located semiC $ do
        et <- check e
        s <- get
        let FunSig rt _ = ctxFun $ context s
        ensureAssignable rt et
    check (VRet semiC) = located semiC $ do
        s <- get
        let FunSig rt _ = ctxFun $ context s
        unless (rt == Void) $ throwError "Type mismatch in return statement"
    check (If tIf e s) = do
        located tIf $ do
            et <- check e
            unless (et == TPrim Bool) $ throwError "Type mismatch in condition"
        check s
    check (IfElse tIf e s1 s2) = do
        located tIf $ do
            et <- check e
            unless (et == TPrim Bool) $ throwError "Type mismatch in condition"
        check s1
        check s2
    check (While tWhile e s) = do
        located tWhile $ do
            et <- check e
            unless (et == TPrim Bool) $ throwError "Type mismatch in condition"
        check s
    check (For tFor t ident e s) = do
        located tFor $ do
            check t
            et <- check e
            at <- case et of
                TPrimArr p -> return $ TPrim p
                TObjArr i -> return $ TObj i
                otherwise -> throwError "Iterating a non-array value"
            ensureAssignable t at
        withPushedScope empty $ do
            located ident $ define ident t
            check s
    check (SExp e semiC) = do
        located semiC $ check e
        return ()

instance Checkable LVal Type where
    check (LVar ident) = do
        CheckState globals c <- get
        let scopes = ctxScopes c
        let n = name ident
        case find (member n) scopes of
            Just scope -> return $ scope ! n
            Nothing -> case definedByContext c n of
                Just t -> return t
                Nothing -> throwError $ printf "Undefined %s" n
        where
        definedByContext (MethodContext (ClsSig _ items) _ _) n =
            case find (\i -> name i == n) items of
                Just (Attr _ t) -> Just t
                otherwise -> Nothing
        definedByContext _ _ = Nothing
    check (LArr arrE ixE) = do
        ixT <- check ixE
        unless (ixT == TPrim Int) $ throwError "Array index must be an integer"
        arrT <- check arrE
        case arrT of
            TPrimArr p -> return $ TPrim p
            TObjArr i -> return $ TObj i
            otherwise -> throwError "Indexing a non-array value"
    check (LAttr e ident) = do
        objT <- check e
        case objT of
            TObj clsIdent -> do
                s <- get
                handleObject $ classes (globals s) ! name clsIdent
            TPrimArr p -> handleArray $ TPrim p
            TObjArr i -> handleArray $ TObj i
            otherwise -> throwError "Attribute access on non-object"
        where
        handleObject clsSig =
            case find (\i -> name i == name ident) $ clsItems clsSig of
                Just (Attr _ t) -> return t
                otherwise -> throwError $ printf
                    "No attribute: %s" (name ident)
        handleArray t =
            if name ident == "length"
                then return t
                else throwError "Arrays have only length attribute"

checkBinOp :: Primitive -> Primitive -> Expr -> Expr -> String -> Check Type
checkBinOp argP retP arg1 arg2 opName = do
    t1 <- check arg1
    t2 <- check arg2
    let argT = TPrim argP
    unless (t1 == argT && t2 == argT) $ throwError $ printf
            "Type mismatch in %s operation" opName
    return $ TPrim retP

instance Checkable Expr Type where
    check (ELitInt _) = return $ TPrim Int
    check (EString _) = return $ TPrim Str
    check ELitTrue = return $ TPrim Bool
    check ELitFalse = return $ TPrim Bool
    check ENull = return BaseObject
    check ESelf = do
        s <- get
        case context s of
            MethodContext clsSig _ _ ->
                return $ TObj $ mkId $ head $ superNames clsSig
            otherwise -> throwError "self outside of a method"
    check (ELVal lVal) = check lVal
    check (ECall ident args) = do
        argTs <- mapM check args
        s <- get
        funSig <- case Data.Map.lookup (name ident) (functions $ globals s) of
            Just fs -> return fs
            Nothing -> throwError $ printf "No function: %s" (name ident)
        let sigArgTs = funSigArgTs funSig
        unless (length argTs == length sigArgTs) $ throwError
            "Bad number of arguments in function call"
        mapM_ (uncurry ensureAssignable) (zip sigArgTs argTs)
        return $ funSigRetT funSig
    check (EMethCall e ident args) = do
        objT <- check e
        clsSig <- case objT of
            TObj clsIdent -> do
                s <- get
                return $ classes (globals s) ! name clsIdent
            otherwise -> throwError "Method call on non-object"
        funSig <- case find (\i -> name i == name ident) $ clsItems clsSig of
            Just (Method _ fs) -> return fs
            otherwise -> throwError $ printf "No method: %s" (name ident)
        argTs <- mapM check args
        let sigArgTs = funSigArgTs funSig
        unless (length argTs == length sigArgTs) $ throwError
            "Bad number of arguments in method call"
        mapM_ (uncurry ensureAssignable) (zip sigArgTs argTs)
        return $ funSigRetT funSig
    check (ENewObj ident) = let r = TObj ident in do
        check r
        return r
    check (ENewArr t e) = do
        check t
        let r = case t of
                TPrim p -> TPrimArr p
                TObj i -> TObjArr i
        sizeT <- check e
        case sizeT of
                TPrim Int -> return r
                otherwise -> throwError "Array size must be an integer"
    check (ENullCast ident) = let r = TObj ident in do
        check r
        return r
    check (Neg e) = do
        t <- check e
        unless (t == TPrim Int) $ throwError
                "Arithmetic operation on non-integer"
        return t
    check (Not e) = do
        t <- check e
        unless (t == TPrim Bool) $ throwError
                "Logical operation on non-bool"
        return t
    check (EMul e1 op e2) = checkBinOp Int Int e1 e2 $ show op
    check (EAdd e1 Plus e2) = do
        t1 <- check e1
        t2 <- check e2
        unless (t1 == t2 && (t1 == TPrim Int || t1 == TPrim Str)) $ throwError
                "Type mismatch in Plus operation"
        return t1
    check (EAdd e1 Minus e2) = checkBinOp Int Int e1 e2 $ show Minus
    check (ERel e1 op e2) = case op of
        EQU -> handleEq
        NE -> handleEq
        otherwise -> checkBinOp Int Bool e1 e2 $ show op
        where
        isPrimitive (TPrim _) = True
        isPrimitive _ = False

        handleEq = do
            t1 <- check e1
            t2 <- check e2
            let ok = if isPrimitive t1
                then t1 == t2
                else not $ isPrimitive t2
            unless ok $ throwError $ printf
                    "Type mismatch in %s operation" (show op)
            return $ TPrim Bool
    check (EAnd e1 e2) = checkBinOp Bool Bool e1 e2 "And"
    check (EOr e1 e2) = checkBinOp Bool Bool e1 e2 "Or"

