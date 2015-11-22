module Check (checkProgramReturningGlobals) where

import Control.Monad (foldM, unless)
import Control.Monad.Except (
    catchError, Except, MonadError, runExcept, throwError)
import Control.Monad.State (MonadState, StateT, evalStateT, get, state)
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
    | FunctionContext FunSig [Scope]
    | MethodContext ClsSig FunSig [Scope]
    deriving (Show)

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

checkType :: Type -> Check ()
checkType (TPrim p) = return ()
checkType (TObj pIdent) = let clsName = name pIdent in do
    s <- get
    unless (member clsName $ classes $ globals s) $ throwError $ printf
        "Undefined: %s (line %d)" clsName (lineNo pIdent)
checkType (TPrimArr p) = return ()
checkType (TObjArr clsIdent) = checkType (TObj clsIdent)

checkNonVoidType :: PIdent -> Type -> Check ()
checkNonVoidType pIdent (TPrim Void) = throwError $ printf
        "Void is not allowed as attribute or argument type (line %d)"
        (lineNo pIdent)
checkNonVoidType _ t = checkType t

-- checkable

class Checkable a where
    check :: a -> Check ()

instance Checkable Program where
    check (Program topDefs) = do
        -- ensure top defs have unique identifiers
        ensureUnique $ map pIdent topDefs
        -- put signatures of functions and classes to state
        topoClsOrder <- checkClsExtTree clsDefs clsExtDefs
        clsSigMap <- foldM addClsSig empty topoClsOrder
        let globals = Globals clsSigMap  (fromList
                [(name fd, makeFunSig fd) | GlFunDef fd <- funDefs])
        unless (Data.Map.lookup "main" (functions globals)
                == Just (FunSig (TPrim Int) []))
            $ throwError "No definition of global function: int main()"
        state (\s -> ((), CheckState globals (context s)))
        -- check each function and class
        mapM_ check topDefs
        return ()
        where
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

            makeFunSig funDef = FunSig
                (returnType funDef) (map argType (funArgs funDef))

            makeClsSigItem :: ClsDefItem -> ClsSigItem
            makeClsSigItem (AttrDef t pIdent _) = Attr (name pIdent) t
            makeClsSigItem (MethDef funDef) = Method (name funDef)
                    (makeFunSig funDef)

            mergeClsSigItems :: [ClsSigItem] -> [ClsSigItem]
                -> Check [ClsSigItem]
            mergeClsSigItems mergedItems [] = return mergedItems
            mergeClsSigItems mergedItems (clsItem : leftItems) =
                let found = find (\i -> name i == name clsItem) mergedItems
                in case (clsItem, found) of
                    (_, Nothing) ->
                        mergeClsSigItems (mergedItems ++ [clsItem]) leftItems
                    (Method _ s1, Just (Method _ s2)) | s1 == s2 ->
                        mergeClsSigItems mergedItems leftItems
                    otherwise -> throwError $ printf
                        "Incorrect redefinition of %s" (name clsItem)
                
            addClsSig :: Map String ClsSig -> TopDef
                -> Check (Map String ClsSig)
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

instance Checkable TopDef where
    check (GlFunDef funDef) = check funDef
    check clsDef = do
        ensureUnique $ map pIdent $ items clsDef
        mapM_ checkItem $ items clsDef
        return ()
        where
            checkItem (AttrDef t pIdent _) = checkNonVoidType pIdent t
            checkItem (MethDef funDef) = check funDef

instance Checkable FunDef where
    check funDef = do
        checkType $ returnType funDef
        ensureUnique $ map pIdent (funArgs funDef)
        mapM_ (checkNonVoidType (funName funDef) . argType) (funArgs funDef)
        check $ body funDef
        return ()

instance Checkable Block where
    check (Block stmts) = mapM_ check stmts

instance Checkable Stmt where
    check _ = return () -- TODO


