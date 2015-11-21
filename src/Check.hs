module Check (checkProgramReturningGlobals) where

import Control.Monad (unless)
import Control.Monad.Except (Except, MonadError, runExcept, throwError)
import Control.Monad.State (MonadState, StateT, evalStateT, get, state)
import Data.Foldable (Foldable)
import qualified Data.Foldable (elem)
import Data.List (nub, partition)
import Data.Map (empty, fromList)
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
        "Undefined: %s" clsName
checkTypeGivenClsNames _ (TPrimArr p) = return ()
checkTypeGivenClsNames clsNames (TObjArr clsIdent) =
    checkTypeGivenClsNames clsNames (TObj clsIdent)

-- checkable

class Checkable a where
    check :: a -> Check ()

instance Checkable Program where
    check (Program topDefs) = do
        ensureUnique $ map pIdent topDefs
        checkClsExtTree (map name clsDefs) clsExtDefs
        funSigs <- mapM (makeFunSig . funDef) funDefs
        clsSigs <- mapM makeClsSig nonFunDefs
        let globals = Globals
                (fromList $ zip (map name nonFunDefs) clsSigs)
                (fromList $ zip (map name funDefs) funSigs)
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

            checkClsExtTree :: [String] -> [TopDef] -> Check ()
            checkClsExtTree _ [] = return ()
            checkClsExtTree [] (c : _) = throwError $ printf
                    "Cannot resolve class inheritance (line %d)"
                    (lineNo $ pIdent c)
            checkClsExtTree (currentName : checkedNames) unchecked = do
                let (ok, rest) = partition
                        (\c -> name (super c) == currentName)
                        unchecked
                checkClsExtTree (map name ok ++ checkedNames) rest

            clsNames :: [String]
            clsNames = map name nonFunDefs

            makeFunSig :: FunDef -> Check FunSig
            makeFunSig funDef = do
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

            makeClsSig :: TopDef -> Check ClsSig
            makeClsSig (ClsDef _ items) = do
                sigItems <- mapM makeClsSigItem items
                return $ ClsSig Nothing sigItems
            makeClsSig (ClsExtDef _ superPIdent items) = do
                sigItems <- mapM makeClsSigItem items
                return $ ClsSig (Just $ name superPIdent) sigItems

instance Checkable TopDef where
    check _ = return () -- TODO

