{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
module Parser.PrintLatte where

-- pretty-printer generated by the BNF converter

import Parser.AbsLatte
import Data.Char


-- the top-level printing method
printTree :: Print a => a -> String
printTree = render . prt 0

type Doc = [ShowS] -> [ShowS]

doc :: ShowS -> Doc
doc = (:)

render :: Doc -> String
render d = rend 0 (map ($ "") $ d []) "" where
  rend i ss = case ss of
    "["      :ts -> showChar '[' . rend i ts
    "("      :ts -> showChar '(' . rend i ts
    "{"      :ts -> showChar '{' . new (i+1) . rend (i+1) ts
    "}" : ";":ts -> new (i-1) . space "}" . showChar ';' . new (i-1) . rend (i-1) ts
    "}"      :ts -> new (i-1) . showChar '}' . new (i-1) . rend (i-1) ts
    ";"      :ts -> showChar ';' . new i . rend i ts
    t  : "," :ts -> showString t . space "," . rend i ts
    t  : ")" :ts -> showString t . showChar ')' . rend i ts
    t  : "]" :ts -> showString t . showChar ']' . rend i ts
    t        :ts -> space t . rend i ts
    _            -> id
  new i   = showChar '\n' . replicateS (2*i) (showChar ' ') . dropWhile isSpace
  space t = showString t . (\s -> if null s then "" else (' ':s))

parenth :: Doc -> Doc
parenth ss = doc (showChar '(') . ss . doc (showChar ')')

concatS :: [ShowS] -> ShowS
concatS = foldr (.) id

concatD :: [Doc] -> Doc
concatD = foldr (.) id

replicateS :: Int -> ShowS -> ShowS
replicateS n f = concatS (replicate n f)

-- the printer class does the job
class Print a where
  prt :: Int -> a -> Doc
  prtList :: [a] -> Doc
  prtList = concatD . map (prt 0)

instance Print a => Print [a] where
  prt _ = prtList

instance Print Char where
  prt _ s = doc (showChar '\'' . mkEsc '\'' s . showChar '\'')
  prtList s = doc (showChar '"' . concatS (map (mkEsc '"') s) . showChar '"')

mkEsc :: Char -> Char -> ShowS
mkEsc q s = case s of
  _ | s == q -> showChar '\\' . showChar s
  '\\'-> showString "\\\\"
  '\n' -> showString "\\n"
  '\t' -> showString "\\t"
  _ -> showChar s

prPrec :: Int -> Int -> Doc -> Doc
prPrec i j = if j<i then parenth else id


instance Print Integer where
  prt _ x = doc (shows x)


instance Print Double where
  prt _ x = doc (shows x)



instance Print TIf where
  prt _ (TIf (_,i)) = doc (showString ( i))


instance Print TWhile where
  prt _ (TWhile (_,i)) = doc (showString ( i))


instance Print TFor where
  prt _ (TFor (_,i)) = doc (showString ( i))


instance Print PIdent where
  prt _ (PIdent (_,i)) = doc (showString ( i))


instance Print SemiC where
  prt _ (SemiC (_,i)) = doc (showString ( i))



instance Print Program where
  prt i e = case e of
   Program topdefs -> prPrec i 0 (concatD [prt 0 topdefs])


instance Print TopDef where
  prt i e = case e of
   GlFunDef fundef -> prPrec i 0 (concatD [prt 0 fundef])
   ClsDef pident clsdefitems -> prPrec i 0 (concatD [doc (showString "class") , prt 0 pident , doc (showString "{") , prt 0 clsdefitems , doc (showString "}")])
   ClsExtDef pident0 pident clsdefitems -> prPrec i 0 (concatD [doc (showString "class") , prt 0 pident0 , doc (showString "extends") , prt 0 pident , doc (showString "{") , prt 0 clsdefitems , doc (showString "}")])

  prtList es = case es of
   [x] -> (concatD [prt 0 x])
   x:xs -> (concatD [prt 0 x , prt 0 xs])

instance Print FunDef where
  prt i e = case e of
   FunDef type' pident args block -> prPrec i 0 (concatD [prt 0 type' , prt 0 pident , doc (showString "(") , prt 0 args , doc (showString ")") , prt 0 block])
   VoidFunDef pident args block -> prPrec i 0 (concatD [doc (showString "void") , prt 0 pident , doc (showString "(") , prt 0 args , doc (showString ")") , prt 0 block])


instance Print ClsDefItem where
  prt i e = case e of
   AttrDef type' pident semic -> prPrec i 0 (concatD [prt 0 type' , prt 0 pident , prt 0 semic])
   MethDef fundef -> prPrec i 0 (concatD [prt 0 fundef])

  prtList es = case es of
   [] -> (concatD [])
   x:xs -> (concatD [prt 0 x , prt 0 xs])

instance Print Arg where
  prt i e = case e of
   Arg type' pident -> prPrec i 0 (concatD [prt 0 type' , prt 0 pident])

  prtList es = case es of
   [] -> (concatD [])
   [x] -> (concatD [prt 0 x])
   x:xs -> (concatD [prt 0 x , doc (showString ",") , prt 0 xs])

instance Print Stmt where
  prt i e = case e of
   Empty semic -> prPrec i 0 (concatD [prt 0 semic])
   BStmt block -> prPrec i 0 (concatD [prt 0 block])
   Decl type' items semic -> prPrec i 0 (concatD [prt 0 type' , prt 0 items , prt 0 semic])
   Ass lval expr semic -> prPrec i 0 (concatD [prt 0 lval , doc (showString "=") , prt 0 expr , prt 0 semic])
   Incr lval semic -> prPrec i 0 (concatD [prt 0 lval , doc (showString "++") , prt 0 semic])
   Decr lval semic -> prPrec i 0 (concatD [prt 0 lval , doc (showString "--") , prt 0 semic])
   Ret expr semic -> prPrec i 0 (concatD [doc (showString "return") , prt 0 expr , prt 0 semic])
   VRet semic -> prPrec i 0 (concatD [doc (showString "return") , prt 0 semic])
   If tif expr stmt -> prPrec i 0 (concatD [prt 0 tif , doc (showString "(") , prt 0 expr , doc (showString ")") , prt 0 stmt])
   IfElse tif expr stmt0 stmt -> prPrec i 0 (concatD [prt 0 tif , doc (showString "(") , prt 0 expr , doc (showString ")") , prt 0 stmt0 , doc (showString "else") , prt 0 stmt])
   While twhile expr stmt -> prPrec i 0 (concatD [prt 0 twhile , doc (showString "(") , prt 0 expr , doc (showString ")") , prt 0 stmt])
   For tfor type' pident expr stmt -> prPrec i 0 (concatD [prt 0 tfor , doc (showString "(") , prt 0 type' , prt 0 pident , doc (showString ":") , prt 0 expr , doc (showString ")") , prt 0 stmt])
   SExp expr semic -> prPrec i 0 (concatD [prt 0 expr , prt 0 semic])

  prtList es = case es of
   [] -> (concatD [])
   x:xs -> (concatD [prt 0 x , prt 0 xs])

instance Print Block where
  prt i e = case e of
   Block stmts -> prPrec i 0 (concatD [doc (showString "{") , prt 0 stmts , doc (showString "}")])


instance Print Item where
  prt i e = case e of
   NoInit pident -> prPrec i 0 (concatD [prt 0 pident])
   Init pident expr -> prPrec i 0 (concatD [prt 0 pident , doc (showString "=") , prt 0 expr])

  prtList es = case es of
   [x] -> (concatD [prt 0 x])
   x:xs -> (concatD [prt 0 x , doc (showString ",") , prt 0 xs])

instance Print LVal where
  prt i e = case e of
   LVar pident -> prPrec i 0 (concatD [prt 0 pident])
   LArr expr0 expr -> prPrec i 0 (concatD [prt 7 expr0 , doc (showString "[") , prt 0 expr , doc (showString "]")])
   LAttr expr pident -> prPrec i 0 (concatD [prt 7 expr , doc (showString ".") , prt 0 pident])


instance Print Type where
  prt i e = case e of
   TPrim primitive -> prPrec i 0 (concatD [prt 0 primitive])
   TPrimArr primitive -> prPrec i 0 (concatD [prt 0 primitive , doc (showString "[]")])
   TObjArr pident -> prPrec i 0 (concatD [prt 0 pident , doc (showString "[]")])
   TObj pident -> prPrec i 0 (concatD [prt 0 pident])
   Void  -> prPrec i 0 (concatD [])

  prtList es = case es of
   [] -> (concatD [])
   [x] -> (concatD [prt 0 x])
   x:xs -> (concatD [prt 0 x , doc (showString ",") , prt 0 xs])

instance Print Primitive where
  prt i e = case e of
   Int  -> prPrec i 0 (concatD [doc (showString "int")])
   Str  -> prPrec i 0 (concatD [doc (showString "string")])
   Bool  -> prPrec i 0 (concatD [doc (showString "boolean")])


instance Print Expr where
  prt i e = case e of
   ELitInt n -> prPrec i 7 (concatD [prt 0 n])
   EString str -> prPrec i 7 (concatD [prt 0 str])
   ELitTrue  -> prPrec i 7 (concatD [doc (showString "true")])
   ELitFalse  -> prPrec i 7 (concatD [doc (showString "false")])
   ENull  -> prPrec i 7 (concatD [doc (showString "null")])
   ESelf  -> prPrec i 7 (concatD [doc (showString "self")])
   ELVal lval -> prPrec i 7 (concatD [prt 0 lval])
   ECall pident exprs -> prPrec i 7 (concatD [prt 0 pident , doc (showString "(") , prt 0 exprs , doc (showString ")")])
   EMethCall expr pident exprs -> prPrec i 7 (concatD [prt 7 expr , doc (showString ".") , prt 0 pident , doc (showString "(") , prt 0 exprs , doc (showString ")")])
   ENewObj pident -> prPrec i 6 (concatD [doc (showString "new") , prt 0 pident])
   ENewArr type' expr -> prPrec i 6 (concatD [doc (showString "new") , prt 0 type' , doc (showString "[") , prt 0 expr , doc (showString "]")])
   ENullCast pident -> prPrec i 6 (concatD [doc (showString "(") , prt 0 pident , doc (showString ")") , doc (showString "null")])
   Neg expr -> prPrec i 5 (concatD [doc (showString "-") , prt 6 expr])
   Not expr -> prPrec i 5 (concatD [doc (showString "!") , prt 6 expr])
   EMul expr0 mulop expr -> prPrec i 4 (concatD [prt 4 expr0 , prt 0 mulop , prt 5 expr])
   EAdd expr0 addop expr -> prPrec i 3 (concatD [prt 3 expr0 , prt 0 addop , prt 4 expr])
   ERel expr0 relop expr -> prPrec i 2 (concatD [prt 2 expr0 , prt 0 relop , prt 3 expr])
   EAnd expr0 expr -> prPrec i 1 (concatD [prt 2 expr0 , doc (showString "&&") , prt 1 expr])
   EOr expr0 expr -> prPrec i 0 (concatD [prt 1 expr0 , doc (showString "||") , prt 0 expr])

  prtList es = case es of
   [] -> (concatD [])
   [x] -> (concatD [prt 0 x])
   x:xs -> (concatD [prt 0 x , doc (showString ",") , prt 0 xs])

instance Print AddOp where
  prt i e = case e of
   Plus  -> prPrec i 0 (concatD [doc (showString "+")])
   Minus  -> prPrec i 0 (concatD [doc (showString "-")])


instance Print MulOp where
  prt i e = case e of
   Times  -> prPrec i 0 (concatD [doc (showString "*")])
   Div  -> prPrec i 0 (concatD [doc (showString "/")])
   Mod  -> prPrec i 0 (concatD [doc (showString "%")])


instance Print RelOp where
  prt i e = case e of
   LTH  -> prPrec i 0 (concatD [doc (showString "<")])
   LE  -> prPrec i 0 (concatD [doc (showString "<=")])
   GTH  -> prPrec i 0 (concatD [doc (showString ">")])
   GE  -> prPrec i 0 (concatD [doc (showString ">=")])
   EQU  -> prPrec i 0 (concatD [doc (showString "==")])
   NE  -> prPrec i 0 (concatD [doc (showString "!=")])



