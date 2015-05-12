module Evaluation

import All
import Types
import Expressions
import Values

mutual
 evalEnv : All getType g -> All (Exp g) g' -> All getType g'
 evalEnv g xs = mapAll (\ m => eval g m) xs

 evalVar : All getType  g -> Var' g a -> getType a
 evalVar g x = lookup x g

 evalFun : All getType g -> Exp (a :: g) b -> getType a -> getType b
 evalFun g l = \ x => eval (x :: g) l

 eval : All getType g -> Exp g a -> getType a
 eval g (ConI x)    = conI x
 eval g (ConB x)    = conB x
 eval g (ConF x)    = conF x
 eval g (AppV x ns) = appV (evalVar g x) (evalEnv g ns)
 eval g (Cnd l m n) = cnd  (eval g l) (eval g m) (eval g n)
 eval g (Whl l m n) = whl  (evalFun g l) (evalFun g m ) (eval g n)
 eval g (Tpl l m)   = tpl  (eval g l) (eval g m)
 eval g (Fst l)     = fst  (eval g l)
 eval g (Snd l)     = snd  (eval g l)
 eval g (Ary l m)   = ary  (eval g l) (evalFun g m)
 eval g (Len l)     = len  (eval g l)
 eval g (Ind l m)   = ind  (eval g l) (eval g m)
 eval g (Let l m)   = lett (eval g l) (evalFun g m)
 eval g (Cmx l m)   = cmx  (eval g l) (eval g m)
 eval g (Tag x l)   = tag  x (eval g l)
 eval g (Mul l m)   = mul  (eval g l) (eval g m)
 eval g (Add l m)   = add  (eval g l) (eval g m)
 eval g (Sub l m)   = sub  (eval g l) (eval g m)
 eval g (Eql l m)   = eql  (eval g l) (eval g m)
 eval g (Ltd l m)   = ltd  (eval g l) (eval g m)
 eval g (Mem l)     = mem  (eval g l)

ex1 : Float
ex1 = eval [] (Cnd (ConB True) (ConF 1.1) (ConF 42.0))


ifThenElse : Exp g Bol -> Exp g a -> Exp g a -> Exp g a
ifThenElse l m n = Cnd l m n

ex2 : Float
ex2 = eval [] (if ConB True then ConF 1.1 else ConF 42.0)


implicit
Bits32toWrd : Bits32 -> Exp g Wrd
Bits32toWrd = ConI

implicit
BooltoBol : Bool -> Exp g Bol
BooltoBol = ConB

implicit
FloattoFlt : Float -> Exp g Flt
FloattoFlt = ConF

ex3 : Float
ex3 = eval [] (Cnd True 1.1 42.0)

