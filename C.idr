module C

import Prelude
import Types
import Data.List
import Pretty

VarC : Type
VarC = (String , Typ)

data Exp =
   Var String
 | Wrd Bits32
 | Flt Float
 | App String (List Exp)

%name Exp e1,e2,e3,e4

data Stmt =
   If  Exp (List Stmt) (List Stmt)
 | Whl Exp (List Stmt)
 | Assign String Exp
 | Declare VarC
 | Return  Exp

%name Stmt s1,s2,s3,s4

data FunC = MkFunC Typ String (List VarC) (List Stmt)

instance Eq Typ where
  Wrd == Wrd                   = True
  Wrd == _                     = False
  Bol == Bol                   = True
  Bol == _                     = False
  Flt == Flt                   = True
  Flt == t2                    = False
  (Arr t1 t2) == (Arr t1' t2') = t1 == t1' && t2 == t2'
  (Arr t1 t2) == _             = False
  (Tpl t1 t2) == (Tpl t1' t2') = t1 == t1' && t2 == t2'
  (Tpl _  _)  == _             = False
  (Ary t)     == (Ary t')      = t == t'
  (Ary _)     == _             = False
  Cmx         == Cmx           = True
  Cmx         == _             = False

commaCat : List Doc -> Doc
commaCat ds = foldl1 (<>) (intersperse (comma<>space) ds)

partial
printType : Typ -> Doc
printType Wrd        = text "Wrd"
printType Bol        = text "Bol"
printType Flt        = text "Flt"
printType (Tpl t t') = text "Tpl" <> printType t <> printType t'
printType (Ary t)    = text "Ary" <> printType t
printType Cmx        = text "Cmx"

printExp : Exp -> Doc
printExp (Var x)    = text x
printExp (Wrd x)    = text (show x ++ "u")
printExp (Flt x)    = text (show x ++ "f")
printExp (App x xs) = text x <+> parens (commaCat (map printExp xs))

printStmt : Stmt -> Doc
printStmt (If e1 xs ys) = text "if" <+> parens (printExp e1)
  <$$> (lbrace
   <$$> nest 2 (vcat (map printStmt xs))
   <$$> rbrace)
  <$$> text "else"
  <$$> (lbrace
   <$$> nest 2 (vcat (map printStmt ys))
   <$$> rbrace)
printStmt (Whl e ss) = text "while" <+> parens (printExp e)
  <$$> (lbrace
   <$$> nest 2 (vcat (map printStmt ss))
   <$$> rbrace)
printStmt (Assign x e1) = text x <+> text "=" <+> ((printExp e1) <> semi)
printStmt (Declare (x , t)) =  printType t <+> (text x <> semi)
printStmt (Return e1) = text "return" <+> (printExp e1 <> semi)

printVar : VarC -> Doc
printVar (v,t) = printType t <+> text v

printFunC : FunC -> Doc
printFunC (MkFunC ty name vs ss) =
  printType ty <+> text name
  <+> parens (commaCat (map printVar vs) )
  <$$> (lbrace
        <$$> nest 2 (vcat (map printStmt ss))
        <$$> rbrace)
