module Emit (emitProgramGivenGlobals) where

import Control.Monad (when, unless)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.State (MonadState, StateT, evalStateT, get, put, state)
import Data.Char (ord)
import Data.List (elemIndex, find, intercalate)
import Data.Map (Map, empty, fromList, insert, member, (!))
import Data.Maybe (fromJust)
import Text.Printf (printf)

import Parser.AbsLatte
import Types

type Scope = Map String (Type, Int)

data Context =
      NoContext
    | FunctionContext
    { ctxScopes :: [Scope], outBuf :: [String], localsSize :: Int }
    | MethodContext
    { ctxClsName :: String
    , ctxScopes :: [Scope], outBuf :: [String], localsSize :: Int
    } deriving (Show)

setScopes scopes (FunctionContext _ o l) = FunctionContext scopes o l
setScopes scopes (MethodContext c _ o l) = MethodContext c scopes o l

setLocalsSize l (FunctionContext s o _) = FunctionContext s o l
setLocalsSize l (MethodContext c s o _) = MethodContext c s o l

data EmitState = EmitState
    { globals :: Globals
    , literals :: [String]
    , context :: Context
    } deriving (Show)

newtype Emit a
    = Emit (StateT EmitState IO a)
   deriving (Monad, MonadState EmitState, MonadIO)

runEmitMonad :: Emit a -> EmitState -> IO a
runEmitMonad (Emit emit) = evalStateT emit

emitProgramGivenGlobals :: Program -> Globals -> IO ()
emitProgramGivenGlobals p g = runEmitMonad (emit p) $ EmitState g [] NoContext

-- helpers

getLiterals :: Emit [String]
getLiterals = do
    EmitState _ l _ <- get
    return l

itemOffset :: Int -> [ClsSigItem] -> String -> Int
itemOffset offset (it:its) n =
        if n == name it
            then offset
            else itemOffset (offset + itemSize it) its n
        where
            itemSize (Attr _ t) = typeSize t
            itemSize (Method _ _) = 4

sizeIndicator :: Int -> String
sizeIndicator 1 = "byte"
sizeIndicator 4 = "dword"

typeSize :: Type -> Int
typeSize Void = 0
typeSize (TPrim Bool) = 1
typeSize _ = 4

withPushedScope :: Scope -> Emit a -> Emit a
withPushedScope s m = do
    EmitState g1 l1 c1 <- get
    put $ EmitState g1 l1 (setScopes (s:(ctxScopes c1)) c1)
    result <- m
    EmitState g2 l2 c2 <- get
    put $ EmitState g2 l2 (setScopes (tail $ ctxScopes c2) c2)
    return result

withContext c m = do
    EmitState globals l1 oldContext <- get
    put $ EmitState globals l1 c
    result <- m
    l2 <- getLiterals
    put $ EmitState globals l2 oldContext
    return result

-- emitable

class Emitable a t | a -> t where
    emit :: a -> Emit t

instance Emitable String () where
    emit str = do
        EmitState g l c <- get
        case c of
            NoContext -> liftIO $ putStrLn str
            FunctionContext scopes outBuf localsSize -> put $ EmitState g l
                    $ FunctionContext scopes (outBuf ++ [str]) localsSize
            MethodContext c scopes outBuf localsSize -> put $ EmitState g l
                    $ MethodContext c scopes (outBuf ++ [str]) localsSize

instance Emitable Program () where
    emit (Program topDefs) = do
        emit "global main"
        emit "\n"
        emit "section .text"
        emit "extern g_printInt,g_printString,g_error,g_readInt,g_readString"
        emit "extern i_concat" -- TODO
        emit "\n"

        mapM_ emit topDefs

        emit "section .data"

        s <- get
        mapM_ emitLit (zip [0..] $ literals s)

        where
        emitLit :: (Int, String) -> Emit ()
        emitLit (ix, l) = emit (printf "l_%d db %s"
            ix (intercalate "," $ map (show . ord) $ l ++ "\0") :: String)

instance Emitable TopDef () where
    emit (GlFunDef funDef) = do
        when (name funDef == "main") $ emit "main:"
        emit (printf "g_%s:" (name funDef) :: String)
        emit "    push ebp"
        emit "    mov ebp, esp"

        let args = funArgs funDef
        let args_scope = fromList $ zip
                (map (\(Arg _ ident) -> name ident) args)
                $ zip
                    (map (\(Arg t _) -> t) args)
                    (scanl (\ls -> \(Arg t _) -> typeSize t + ls) 8 args)

        withContext (FunctionContext [args_scope] [] 0) $ do
            emit (body funDef)
            s <- get
            let ls = localsSize $ context s
            -- TODO memset locals to 0
            when (ls > 0) $ liftIO $ putStrLn $ printf "    sub esp, %d" ls
            mapM_ (liftIO . putStrLn) (outBuf $ context s)
            when (ls > 0) $ liftIO $ putStrLn $ printf "    add esp, %d" ls

        emit "    pop ebp"
        emit "    ret"
        emit "\n"
    emit clsDef = mapM_ checkItem $ items clsDef
        where
        checkItem (AttrDef _ _ _) = return ()
        checkItem (MethDef funDef) = do
            emit (printf "m___%s___%s:" (name clsDef) (name funDef) :: String)
            emit "    push ebp"
            emit "    mov ebp, esp"

            let args = funArgs funDef
            let args_scope = fromList $ zip
                    (map (\(Arg _ ident) -> name ident) args)
                    $ zip
                        (map (\(Arg t _) -> t) args)
                        (scanl (\ls -> \(Arg t _) -> typeSize t + ls) 12 args)
            withContext (MethodContext (name clsDef) [args_scope] [] 0) $ do
                emit (body funDef)
                s <- get
                let ls = localsSize $ context s
                -- TODO memset locals to 0
                when (ls > 0) $ liftIO $ putStrLn $ printf "    sub esp, %d" ls
                mapM_ (liftIO . putStrLn) (outBuf $ context s)
                when (ls > 0) $ liftIO $ putStrLn $ printf "    add esp, %d" ls

            emit "    pop ebp"
            emit "    ret"
            emit "\n"

instance Emitable Block () where
    emit (Block stmts) = withPushedScope empty $ mapM_ emit stmts

instance Emitable Stmt () where
    emit (Empty _) = return ()
    emit (BStmt block) = emit block
    emit (Decl t items semiC) = mapM_ emitItem items
        where
        emitItem (NoInit ident) = define (name ident)
        emitItem (Init ident e) = do
            define (name ident)
            emit (Ass (LVar ident) e semiC)
        define n = do
            EmitState g1 l1 c1 <- get
            let (sc:scs) = ctxScopes c1
            let nls = localsSize c1 + typeSize t
            let nsc = insert n (t, -nls) sc
            let c2 = setScopes (nsc:scs) $ setLocalsSize nls c1
            put $ EmitState g1 l1 c2
    emit (Ass lv e _) = return () -- TODO
    emit (Incr lv _) = return () -- TODO
    emit (Decr lv _) = return () -- TODO
    emit (Ret e _) = return () -- TODO
    emit (VRet _) = return () -- TODO
    emit (If _ e s) = return () -- TODO
    emit (IfElse _ e s1 s2) = return () -- TODO
    emit (While _ e s) = return () -- TODO
    emit (For _ t ident e s) = return () -- TODO
    emit (SExp e _) = do
        t <- emit e
        let ts = typeSize t
        unless (ts == 0) $ emit $ (printf "    add esp, %d" ts :: String)

instance Emitable LVal Type where
    emit (LVar ident) = do
        s <- get
        let scopes = ctxScopes $ context s
        let n = name ident
        case find (member n) scopes of
            Just scope -> let (t, addr) = scope ! n in do
                emit (if addr >= 0
                    then printf "    lea eax, [ebp+%d]" addr
                    else printf "    lea eax, [ebp%d]" addr :: String)
                emit $ "    push dword eax"
                return t
            Nothing -> do
                s <- get
                let clsSig = (classes $ globals s) ! (ctxClsName $ context s)
                let items = clsItems clsSig
                let offset = itemOffset 0 items n
                emit "    lea eax, [bsp+8]"
                emit "    mov eax, [eax]"
                emit (printf "    add eax, %d" offset :: String)
                emit "    push eax"
                let (Just (Attr _ t)) = find (((==) n) . name) items
                return t
    emit _ = return Void -- TODO

instance Emitable Expr Type where
    emit (ELitInt i) = do
        emit (printf "    push dword %d" i :: String)
        return $ TPrim Int
    emit (EString s) = do
        EmitState g l c <- get
        ix <- case (s `elemIndex` l) of
            Just ix -> return ix
            Nothing -> do
                let ix = length l
                put $ EmitState g (l ++ [s]) c
                return ix
        emit (printf "    push l_%d" ix :: String)
        return $ TPrim Str
    emit ELitTrue = do
        emit "    push byte 1"
        return $ TPrim Bool
    emit ELitFalse = do
        emit "    push byte 0"
        return $ TPrim Bool
    emit ENull = do
        emit "    push dword 0"
        return BaseObject
    emit ESelf = do
        emit "    push dword [bsp + 8]"
        s <- get
        return $ TObj $ mkId $ ctxClsName $ context s
    emit (ELVal lVal) = do
        t <- emit lVal
        emit "    pop eax"
        emit (printf "    push %s [eax]"
                (sizeIndicator (typeSize t)) :: String)
        return t
    emit (ECall ident args) = do
        argTypes <- mapM emit (reverse args)
        emit (printf "    call g_%s" (name ident) :: String)
        let argsSize = sum $ map typeSize argTypes
        unless (argsSize == 0)
                $ emit (printf "    add esp, %d" argsSize :: String)
        s <- get
        let retType = funSigRetT $ (functions $ globals s) ! (name ident)
        case typeSize retType of
            0 -> return ()
            1 -> emit "    push al"
            4 -> emit "    push eax"
        return retType
    emit _ = return Void -- TODO
