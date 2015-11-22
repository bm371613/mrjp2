module Check (checkProgramReturningGlobals) where

import Control.Monad (foldM, unless)
import Control.Monad.Except (
    catchError, Except, MonadError, runExcept, throwError)
import Control.Monad.State (MonadState, StateT, evalStateT, get, state)
import Data.Foldable (Foldable, find)
import qualified Data.Foldable (elem)
import Data.List (nub, partition)
import Data.Map (empty, fromList, insert, Map, (!))
import qualified Data.Map (lookup)
import GHC.Exts (sortWith)
import Text.Printf (printf)

import Parser.AbsLatte
import Types

-- check monad

type Context = ()

data CheckState = CheckState
    { globals :: Globals
    , context :: Context
    } deriving (Show)
emptyCheckState = CheckState (Globals empty empty) ()

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

checkTypeGivenClsNames :: Foldable c => c String -> Type -> Check ()
checkTypeGivenClsNames _ (TPrim p) = return ()
checkTypeGivenClsNames clsNames (TObj pIdent) = let clsName = name pIdent in
    unless (clsName `Data.Foldable.elem` clsNames) $ throwError $ printf
        "Undefined: %s (line %d)" clsName (lineNo pIdent)
checkTypeGivenClsNames _ (TPrimArr p) = return ()
checkTypeGivenClsNames clsNames (TObjArr clsIdent) =
    checkTypeGivenClsNames clsNames (TObj clsIdent)

-- checkable

class Checkable a where
    check :: a -> Check ()

instance Checkable Program where
    check (Program topDefs) = do
        ensureUnique $ map pIdent topDefs
        topoClsOrder <- checkClsExtTree clsDefs clsExtDefs
        funSigs <- mapM (makeFunSig . funDef) funDefs
        clsSigMap <- foldM addClsSig empty topoClsOrder
        let globals = Globals
                clsSigMap
                (fromList $ zip (map name funDefs) funSigs)
        unless (Data.Map.lookup "main" (functions globals)
                == Just (FunSig (TPrim Int) []))
            $ throwError "No definition of global function: int main()"
        state (\s -> ((), CheckState globals (context s)))
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

            clsNames :: [String]
            clsNames = map name nonFunDefs

            makeFunSig :: FunDef -> Check FunSig
            makeFunSig funDef = do
                ensureUnique $ map argName (funArgs funDef)
                let ret = returnType funDef
                let args = map argType (funArgs funDef)
                checkTypeGivenClsNames clsNames ret
                mapM_ (checkTypeGivenClsNames clsNames) args
                return $ FunSig ret args

            makeClsSigItem :: ClsDefItem -> Check ClsSigItem
            makeClsSigItem (AttrDef t pIdent _) = do
                checkTypeGivenClsNames clsNames t
                return $ Attr (name pIdent ) t
            makeClsSigItem (MethDef funDef) = do
                funSig <- makeFunSig funDef
                return $ Method (name funDef) funSig

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
            addClsSig sigs (ClsDef clsIdent items) = do
                ensureUnique $ map pIdent items
                sigItems <- mapM makeClsSigItem items
                return $ insert (name clsIdent)
                    (ClsSig [name clsIdent] sigItems) sigs
            addClsSig sigs (ClsExtDef clsIdent superIdent items) = do
                ensureUnique $ map pIdent items
                let superSig = sigs ! name superIdent
                allSigItems <- mapM makeClsSigItem items
                sigItems <- catchError
                    (mergeClsSigItems (clsItems superSig) allSigItems)
                    (\e -> throwError $ printf "%s\n\tin class %s (line %d)"
                        e (name clsIdent) (lineNo clsIdent))
                return $ insert (name clsIdent)
                    (ClsSig (name clsIdent:superNames superSig) sigItems) sigs

instance Checkable TopDef where
    check _ = return () -- TODO

