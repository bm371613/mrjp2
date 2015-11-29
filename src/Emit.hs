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

data Emited = Line String
    | Push String | Pop String
    | Label String | Jump String deriving (Show)

data Context = Context
    { ctxClsName :: Maybe String
    , ctxFunName :: String
    , ctxScopes :: [Scope]
    , ctxOutBuf :: [Emited]
    , ctxLocalsSize :: Int
    , ctxNextLabel :: Int
    } deriving (Show)

setScopes s (Context c f _ o ls nl) = Context c f s o ls nl
setOutBuf o (Context c f s _ ls nl) = Context c f s o ls nl
setLocalsSize ls (Context c f s o _ nl) = Context c f s o ls nl
setNextLabel nl (Context c f s o ls _) = Context c f s o ls nl

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
emitBuf :: String -> Emit ()
emitBuf str = do
    c <- getContext
    setContext $ setOutBuf (ctxOutBuf c ++ [Line str]) c

emitUnBuf :: String -> Emit ()
emitUnBuf str = liftIO $ putStrLn str

flush :: Emit ()
flush = do
    c <- getMaybeContext
    case c of
        Nothing -> return ()
        Just c -> do
            mapM_ (liftIO . printOut) (optimize $ ctxOutBuf c)
            setContext $ setOutBuf [] c
    where
    printOut (Line str) = putStrLn str
    printOut (Push str) = putStrLn $ printf "    push %s" str
    printOut (Pop str) = putStrLn $ printf "    pop %s" str
    printOut (Label l) = putStrLn $ printf "%s:" l
    printOut (Jump l) = putStrLn $ printf "    jmp %s" l

    cancel f@(Push s1) s@(Pop s2) = if s1 == s2 then ([], []) else ([f], [s])
    cancel f@(Pop s1) s@(Push s2) = if s1 == s2 then ([], []) else ([f], [s])
    cancel f@(Jump l1) s@(Label l2) =
        if l1 == l2 then ([s], []) else ([f], [s])
    cancel f s = ([f], [s])
   
    optimize [] = []
    optimize (emited:[]) = [emited]
    optimize (e1:e2:es) = 
        let (l, r) = cancel e1 e2 in l ++ (optimize (r ++ es))

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

mkLabel :: Emit String
mkLabel = do
    c <- getContext
    prefix <- mkPrologLabel
    let labelIx = ctxNextLabel c
    setContext $ setNextLabel (labelIx + 1) c
    return $ printf "%s___%d" prefix labelIx

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
    return $ printf "%s___epilog" l

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

instance Emitable Emited () where
    emit e = do
        c <- getContext
        setContext $ setOutBuf (ctxOutBuf c ++ [e]) c

instance Emitable Program () where
    emit (Program topDefs) = do
        emitUnBuf "global main"
        emitUnBuf "\n"
        emitUnBuf "section .text"
        emitUnBuf
            "extern g_printInt,g_printString,g_error,g_readInt,g_readString"
        emitUnBuf "extern i_concat" -- TODO
        emitUnBuf "\n"

        mapM_ emit topDefs

        emitUnBuf "section .data"

        s <- get
        mapM_ emitLit (zip [0..] $ literals s)

        where
        emitLit :: (Int, String) -> Emit ()
        emitLit (ix, l) = emitUnBuf $ printf "l_%d db %s"
            ix (intercalate "," $ map (show . ord) $ l ++ "\0")

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
            when (n == "main") $ emitUnBuf "main:"
            mkPrologLabel >>= (\l -> emitUnBuf $ printf "%s:" l)
            emitUnBuf "    push ebp"
            emitUnBuf "    mov ebp, esp"
            emit (body funDef)
            c <- getContext
            let ls = ctxLocalsSize c
            -- TODO memset locals to 0
            when (ls > 0) $ emitUnBuf $ printf "    sub esp, %d" ls
            mkEpilogLabel >>= (emit . Label)
            flush
            when (ls > 0) $ emitUnBuf $ printf "    add esp, %d" ls
            emitUnBuf "    pop ebp"
            emitUnBuf "    ret"
            emitUnBuf "\n"
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
                mkPrologLabel >>= (\l -> emitUnBuf $ printf "%s:" l)
                emitUnBuf "    push ebp"
                emitUnBuf "    mov ebp, esp"
                emit (body funDef)
                c <- getContext
                let ls = ctxLocalsSize c
                -- TODO memset locals to 0
                when (ls > 0) $ emitUnBuf $ printf "    sub esp, %d" ls
                mkEpilogLabel >>= (emit . Label)
                flush
                when (ls > 0) $ emitUnBuf $ printf "    add esp, %d" ls
                emitUnBuf "    pop ebp"
                emitUnBuf "    ret"
                emitUnBuf "\n"

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
    emit (Ass lv e _) = do
        emit lv
        emit e
        emit $ Pop "eax"
        emit $ Pop "edx"
        emitBuf "    mov [edx], eax"
    emit (Incr lv _) = do
        emit lv
        emit $ Pop "eax"
        emitBuf "    inc dword [eax]"
    emit (Decr lv _) = do
        emit lv
        emit $ Pop "eax"
        emitBuf "    dec dword [eax]"
    emit (Ret e _) = do
        emit e
        emit $ Pop "eax"
        mkEpilogLabel >>= (emit . Jump)
    emit (VRet _) = mkEpilogLabel >>= (emit . Jump)
    emit (If _ e s) = do
        endL <- mkLabel
        emit e
        emit $ Pop "eax"
        emitBuf "    cmp eax,1"
        emitBuf $ printf "    jne %s" endL
        emit s
        emit $ Label endL
    emit (IfElse _ e s1 s2) = do
        elseL <- mkLabel
        endL <- mkLabel
        emit e
        emit $ Pop "eax"
        emitBuf "    cmp eax,1"
        emitBuf $ printf "    jne %s" elseL
        emit s1
        emit $ Jump endL
        emit $ Label elseL
        emit s2
        emit $ Label endL
    emit (While _ e s) = return () -- TODO
    emit (For _ t ident e s) = return () -- TODO
    emit (SExp e _) = do
        t <- emit e
        let ts = typeSize t
        unless (ts == 0) $ emitBuf $ printf "    add esp, %d" ts

instance Emitable LVal Type where
    emit (LVar ident) = do
        c <- getContext
        let scopes = ctxScopes c
        let n = name ident
        case find (member n) scopes of
            Just scope -> let (t, addr) = scope ! n in do
                emitBuf (if addr >= 0
                    then printf "    lea eax, [ebp+%d]" addr
                    else printf "    lea eax, [ebp%d]" addr)
                emit $ Push "eax"
                return t
            Nothing -> do
                s <- get
                let clsSig = (classes $ globals s)
                        ! (fromJust $ ctxClsName c)
                let items = clsItems clsSig
                let offset = itemOffset 0 items n
                emitBuf "    lea eax, [bsp+8]"
                emitBuf "    mov eax, [eax]"
                emitBuf $ printf "    add eax, %d" offset
                emit $ Push "eax"
                let (Just (Attr _ t)) = find (((==) n) . name) items
                return t
    emit _ = return Void -- TODO

instance Emitable Expr Type where
    emit (ELitInt i) = do
        emitBuf $ printf "    push %d" i
        return $ TPrim Int
    emit (EString s) = do
        EmitState g l c <- get
        ix <- case (s `elemIndex` l) of
            Just ix -> return ix
            Nothing -> do
                let ix = length l
                put $ EmitState g (l ++ [s]) c
                return ix
        emitBuf $ printf "    lea eax, [l_%d]" ix
        emit $ Push "eax"
        return $ TPrim Str
    emit ELitTrue = let t = TPrim Bool in do
        emitBuf "    push 1"
        return t
    emit ELitFalse = let t = TPrim Bool in do
        emitBuf "    push 0"
        return t
    emit ENull = let t = BaseObject in do
        emitBuf "    push 0"
        return t
    emit ESelf = do
        c <- getContext
        let t = TObj $ mkId $ fromJust $ ctxClsName c
        emitBuf "    push dword [bsp+8]"
        return t
    emit (ELVal lVal) = do
        t <- emit lVal
        emit $ Pop "eax"
        emitBuf "    push dword [eax]"
        return t
    emit (ECall ident args) = do
        argTypes <- mapM emit (reverse args)
        emitBuf $ printf"    call %s" (mkFnLabel $ name ident)
        let argsSize = sum $ map typeSize argTypes
        unless (argsSize == 0)
                $ emitBuf $ printf "    add esp, %d" argsSize
        s <- get
        let retType = funSigRetT $ (functions $ globals s) ! (name ident)
        case typeSize retType of
            0 -> return ()
            4 -> emit $ Push "eax"
        return retType
    emit _ = return Void -- TODO
