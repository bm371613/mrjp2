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

data Context = Context
    { ctxClsName :: Maybe String
    , ctxFunName :: String
    , ctxScopes :: [Scope]
    , ctxOutBuf :: [String]
    , ctxLocalsSize :: Int
    , ctxNextLabel :: Int
    } deriving (Show)

setScopes s (Context c f _ o ls nl) = Context c f s o ls nl
setOutBuf o (Context c f s _ ls nl) = Context c f s o ls nl
setLocalsSize ls (Context c f s o _ nl) = Context c f s o ls nl

data EmitState = EmitState
    { globals :: Globals
    , literals :: [String]
    , context :: Maybe Context
    } deriving (Show)

newtype Emit a
    = Emit (StateT EmitState IO a)
   deriving (Monad, MonadState EmitState, MonadIO)

runEmitMonad :: Emit a -> EmitState -> IO a
runEmitMonad (Emit emit) = evalStateT emit

emitProgramGivenGlobals :: Program -> Globals -> IO ()
emitProgramGivenGlobals p g = runEmitMonad (emit p) $ EmitState g [] Nothing

-- helpers

flush :: Emit ()
flush = do
    c <- getMaybeContext
    case c of
        Nothing -> return ()
        Just c -> do
            mapM_ (liftIO . putStrLn) (ctxOutBuf c)
            setContext $ setOutBuf [] c

getMaybeContext :: Emit (Maybe Context)
getMaybeContext = do
    s <- get
    return $ context s

getContext :: Emit Context
getContext = getMaybeContext >>= (return . fromJust)

setMaybeContext :: Maybe Context -> Emit ()
setMaybeContext c = do
    EmitState g l _ <- get
    put $ EmitState g l c

setContext :: Context -> Emit ()
setContext = setMaybeContext . Just

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

mkFnLabel :: String -> String
mkFnLabel f = printf "g_%s" f

mkMthdLabel :: String -> String -> String
mkMthdLabel c f = printf "m_%s___%s" c f

mkPrologLabel :: Emit String
mkPrologLabel  = do
    c <- getContext
    return $ case ctxClsName c of
        Nothing -> mkFnLabel $ ctxFunName c
        Just cls -> mkMthdLabel cls $ ctxFunName c

mkEpilogLabel :: Emit String
mkEpilogLabel = do
    l <- mkPrologLabel
    return $ printf "e%s" l

typeSize :: Type -> Int
typeSize Void = 0
typeSize _ = 4

withPushedScope :: Scope -> Emit a -> Emit a
withPushedScope s m = do
    oldContext <- getContext
    let withPushedOldContext = setScopes (s:(ctxScopes oldContext)) oldContext
    setContext withPushedOldContext
    result <- m
    withPushedNewContext <- getContext
    setContext $
        setScopes (tail $ ctxScopes withPushedNewContext) withPushedNewContext
    return result

withContext c m = do
    old <- getMaybeContext
    setContext c
    result <- m
    setMaybeContext old
    return result

-- emitable

class Emitable a t | a -> t where
    emit :: a -> Emit t

instance Emitable String () where
    emit str = do
        EmitState g l c <- get
        case c of
            Nothing -> liftIO $ putStrLn str
            Just c -> setContext $ setOutBuf (ctxOutBuf c ++ [str]) c

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
        let n = name funDef
        let args = funArgs funDef
        let args_scope = fromList $ zip
                (map (\(Arg _ ident) -> name ident) args)
                $ zip
                    (map (\(Arg t _) -> t) args)
                    (scanl (\ls -> \(Arg t _) -> typeSize t + ls) 8 args)
        withContext (Context Nothing n [args_scope] [] 0 0) $ do
            when (n == "main") $ emit "main:"
            prologLabel <- mkPrologLabel
            emit (printf "%s:" prologLabel :: String)
            emit "    push ebp"
            emit "    mov ebp, esp"
            emit (body funDef)
            c <- getContext
            let ls = ctxLocalsSize c
            -- TODO memset locals to 0
            when (ls > 0) $ liftIO $ putStrLn $ printf "    sub esp, %d" ls
            flush
            when (ls > 0) $ liftIO $ putStrLn $ printf "    add esp, %d" ls
            epilogLabel <- mkEpilogLabel
            emit (printf "%s:" epilogLabel :: String)
            emit "    pop ebp"
            emit "    ret"
            emit "\n"
            flush
    emit clsDef = mapM_ checkItem $ items clsDef
        where
        checkItem (AttrDef _ _ _) = return ()
        checkItem (MethDef funDef) = do
            let n = name funDef
            let args = funArgs funDef
            let args_scope = fromList $ zip
                    (map (\(Arg _ ident) -> name ident) args)
                    $ zip
                        (map (\(Arg t _) -> t) args)
                        (scanl (\ls -> \(Arg t _) -> typeSize t + ls) 12 args)
            withContext (Context
                    (Just $ name clsDef) n [args_scope] [] 0 0) $ do
                prologLabel <- mkPrologLabel
                emit (printf "%s:" prologLabel :: String)
                emit "    push ebp"
                emit "    mov ebp, esp"
                emit (body funDef)
                c <- getContext
                let ls = ctxLocalsSize c
                -- TODO memset locals to 0
                when (ls > 0) $ liftIO $ putStrLn $ printf "    sub esp, %d" ls
                flush
                when (ls > 0) $ liftIO $ putStrLn $ printf "    add esp, %d" ls
                epilogLabel <- mkEpilogLabel
                emit (printf "%s:" epilogLabel :: String)
                emit "    pop ebp"
                emit "    ret"
                emit "\n"
                flush

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
            oldContext <- getContext
            let (sc:scs) = ctxScopes oldContext
            let nls = ctxLocalsSize oldContext + typeSize t
            let nsc = insert n (t, -nls) sc
            let newContext = setScopes (nsc:scs) $ setLocalsSize nls oldContext
            setContext newContext
    emit (Ass lv e _) = return () -- TODO
    emit (Incr lv _) = return () -- TODO
    emit (Decr lv _) = return () -- TODO
    emit (Ret e _) = do
        l <- mkEpilogLabel
        emit e
        emit "    pop eax"
        emit (printf "    jmp %s" l :: String)
    emit (VRet _) = do
        l <- mkEpilogLabel
        emit (printf "    jmp %s" l :: String)
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
        c <- getContext
        let scopes = ctxScopes c
        let n = name ident
        case find (member n) scopes of
            Just scope -> let (t, addr) = scope ! n in do
                emit (if addr >= 0
                    then printf "    lea eax, [ebp+%d]" addr
                    else printf "    lea eax, [ebp%d]" addr :: String)
                emit $ "    push eax"
                return t
            Nothing -> do
                s <- get
                let clsSig = (classes $ globals s)
                        ! (fromJust $ ctxClsName c)
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
        emit (printf "    push %d" i :: String)
        return $ TPrim Int
    emit (EString s) = do
        EmitState g l c <- get
        ix <- case (s `elemIndex` l) of
            Just ix -> return ix
            Nothing -> do
                let ix = length l
                put $ EmitState g (l ++ [s]) c
                return ix
        emit (printf "    lea eax, [l_%d]" ix :: String)
        emit "    push eax"
        return $ TPrim Str
    emit ELitTrue = let t = TPrim Bool in do
        emit "    push 1"
        return t
    emit ELitFalse = let t = TPrim Bool in do
        emit "    push 0"
        return t
    emit ENull = let t = BaseObject in do
        emit "    push 0"
        return t
    emit ESelf = do
        c <- getContext
        let t = TObj $ mkId $ fromJust $ ctxClsName c
        emit "    push dword [bsp+8]"
        return t
    emit (ELVal lVal) = do
        t <- emit lVal
        emit "    pop eax"
        emit "    push dword [eax]"
        return t
    emit (ECall ident args) = do
        argTypes <- mapM emit (reverse args)
        emit (printf "    call %s" (mkFnLabel $ name ident) :: String)
        let argsSize = sum $ map typeSize argTypes
        unless (argsSize == 0)
                $ emit (printf "    add esp, %d" argsSize :: String)
        s <- get
        let retType = funSigRetT $ (functions $ globals s) ! (name ident)
        case typeSize retType of
            0 -> return ()
            4 -> emit "    push eax"
        return retType
    emit _ = return Void -- TODO
