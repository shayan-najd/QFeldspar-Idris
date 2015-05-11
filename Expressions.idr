module Expressions

import Types
import Data.Complex
import All

data Exp : List Typ -> Typ -> Type where
  ConI : Bits32   -> Exp g Wrd
  ConB : Bool  -> Exp g Bol
  ConF : Float -> Exp g Flt
  AppV : Var' g t  -> All (Exp g) (args t) -> Exp g (out t)
  Cnd  : Exp g Bol -> Exp g a -> Exp g a -> Exp g a
  Whl  : Exp (a :: g) Bol -> Exp (a :: g) a ->
         Exp g a -> Exp g a
  Tpl  : Exp g a -> Exp g b -> Exp g (Tpl a b)
  Fst  : Exp g (Tpl a b) -> Exp g a
  Snd  : Exp g (Tpl a b) -> Exp g b
  Ary  : Exp g Wrd -> Exp (Wrd :: g) a -> Exp g (Ary a)
  Len  : Exp g (Ary a) -> Exp g Wrd
  Ind  : Exp g (Ary a) -> Exp g Wrd -> Exp g a
  Let  : Exp g a -> Exp (a :: g) b -> Exp g b
  Cmx  : Exp g Flt -> Exp g Flt -> Exp g Cmx
  Tag  : String -> Exp g a -> Exp g a
  Mul  : {auto isArith : Arith a} -> Exp g a -> Exp g a -> Exp g a
  Add  : {auto isArith : Arith a} -> Exp g a -> Exp g a -> Exp g a
  Sub  : {auto isArith : Arith a} -> Exp g a -> Exp g a -> Exp g a
  Abs  : {auto isArith : Arith a} -> Exp g a -> Exp g a
  Eql  : {auto isEq    : Eq.Eq a} -> Exp g a -> Exp g a -> Exp g Bol
  Ltd  : {auto isOrd   : Ord.Ord a} -> Exp g a -> Exp g a -> Exp g Bol
  Mem  : Exp g a -> Exp g a

%name Exp l,m,n
