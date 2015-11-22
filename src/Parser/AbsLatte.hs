module Parser.AbsLatte where

-- Haskell module generated by the BNF converter


newtype TIf = TIf ((Int,Int),String) deriving (Eq,Ord,Show)
newtype TWhile = TWhile ((Int,Int),String) deriving (Eq,Ord,Show)
newtype TFor = TFor ((Int,Int),String) deriving (Eq,Ord,Show)
newtype PIdent = PIdent ((Int,Int),String) deriving (Eq,Ord,Show)
newtype SemiC = SemiC ((Int,Int),String) deriving (Eq,Ord,Show)
data Program =
   Program [TopDef]
  deriving (Eq,Ord,Show)

data TopDef =
   GlFunDef { funDef :: FunDef }
 | ClsDef { clsName :: PIdent, items :: [ClsDefItem] }
 | ClsExtDef { clsName :: PIdent, super :: PIdent, items :: [ClsDefItem] }
  deriving (Eq,Ord,Show)

data FunDef = FunDef
 { returnType :: Type
 , funName :: PIdent
 , funArgs ::[Arg]
 , body :: Block
 } deriving (Eq,Ord,Show)

data ClsDefItem =
   AttrDef Type PIdent SemiC
 | MethDef FunDef
  deriving (Eq,Ord,Show)

data Arg =
   Arg {argType :: Type, argName :: PIdent }
  deriving (Eq,Ord,Show)

data Stmt =
   Empty SemiC
 | BStmt Block
 | Decl Type [Item] SemiC
 | Ass LVal Expr SemiC
 | Incr LVal SemiC
 | Decr LVal SemiC
 | Ret Expr SemiC
 | VRet SemiC
 | If TIf Expr Stmt
 | IfElse TIf Expr Stmt Stmt
 | While TWhile Expr Stmt
 | For TFor Type PIdent Expr Stmt
 | SExp Expr SemiC
  deriving (Eq,Ord,Show)

data Block =
   Block [Stmt]
  deriving (Eq,Ord,Show)

data Item =
   NoInit PIdent
 | Init PIdent Expr
  deriving (Eq,Ord,Show)

data LVal =
   LVar PIdent
 | LArr Expr Expr
 | LAttr Expr PIdent
  deriving (Eq,Ord,Show)

data Type =
   TPrim Primitive
 | TPrimArr Primitive
 | TObjArr PIdent
 | TObj PIdent
  deriving (Eq,Ord,Show)

data Primitive =
   Int
 | Str
 | Bool
 | Void
  deriving (Eq,Ord,Show)

data Expr =
   ELitInt Integer
 | EString String
 | ELitTrue
 | ELitFalse
 | ENull
 | ESelf
 | ELVal LVal
 | ECall PIdent [Expr]
 | EMethCall Expr PIdent [Expr]
 | ENewObj PIdent
 | ENewArr Type Expr
 | ENullCast PIdent
 | Neg Expr
 | Not Expr
 | EMul Expr MulOp Expr
 | EAdd Expr AddOp Expr
 | ERel Expr RelOp Expr
 | EAnd Expr Expr
 | EOr Expr Expr
  deriving (Eq,Ord,Show)

data AddOp =
   Plus
 | Minus
  deriving (Eq,Ord,Show)

data MulOp =
   Times
 | Div
 | Mod
  deriving (Eq,Ord,Show)

data RelOp =
   LTH
 | LE
 | GTH
 | GE
 | EQU
 | NE
  deriving (Eq,Ord,Show)


-- helpers

class Named a where
    name :: a -> String

class PIdented a where
    pIdent :: a -> PIdent

class Positioned a where
    lineNo :: a -> Int

instance PIdented PIdent where
    pIdent = id

instance PIdented a => Named a where
    name x = let (PIdent (_, name)) = pIdent x in name

instance PIdented a => Positioned a where
    lineNo x = let PIdent ((lineNo, _), _) = pIdent x in lineNo

instance PIdented FunDef where
    pIdent = funName

instance PIdented TopDef where
    pIdent (GlFunDef funDef) = pIdent funDef
    pIdent cls = clsName cls

instance PIdented ClsDefItem where
    pIdent (AttrDef _ pIdent _) = pIdent
    pIdent (MethDef m) = pIdent m

instance PIdented Arg where
    pIdent (Arg _ pIdent) = pIdent

instance Positioned SemiC where
    lineNo (SemiC ((lineNo, _), _)) = lineNo


