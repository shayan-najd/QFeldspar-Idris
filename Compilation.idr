module Compilation

import Types
import Control.Monad.State
import All
import C
import Expressions
import Pretty

-- a monad for compilation process which carries
--  (a) a number used for generating fresh names
--  (b) a list of parameters  (variables introduced by function header)
--  (c) a list of declared local variables
CompileMonad : Type -> Type
CompileMonad = State (Int , List VarC , List VarC)

-- generates fresh name in the CompileMonad
newName : CompileMonad String
newName = do (i , ps , vs) <- get
             put (i+1 , ps , vs)
             return ("v" ++ show i)

-- generates a fresh parameter name by the given type, and adds it to list of paramters in the monad
newParam : Typ -> CompileMonad String
newParam a = do v <- newName
                (i , ps , vs) <- get
                put (i , (v , a) :: ps , vs)
                return v

-- generates a fresh variable name by the given type, and adds it to list of paramters in the monad
newVar : Typ -> CompileMonad String
newVar a = do v <- newName
              (i , ps , vs) <- get
              put (i , ps , (v , a) :: vs)
              return v

mutual
 -- compiles a list of expressions by concatenating their statements
 compileEnv : All (const String) g -> All (Exp g) (a :: as) -> CompileMonad (List C.Exp, List Stmt)
 compileEnv g (l :: [])    = do (el , sl) <- compileExp g l
                                return ([el] , sl)
 compileEnv g (l :: ls@(_ :: _))
                           = do (el  , sl)  <- compileExp g l
                                (els , sls) <- compileEnv g ls
                                return (el :: els , sl ++ sls)

 -- compiles a term into a pair of a C expression, which returns the resulting computation, and
 -- a set of C statements that does the computation
 compileExp : {a : Typ} -> All (const String) g -> Exp g a -> CompileMonad (C.Exp , List Stmt)
 compileExp     g (ConI x)    = return (Wrd x , [])
 compileExp     g (ConB x)    = return (Var (if x then "true" else "false") , [])
 compileExp     g (ConF x)    = return (Flt x , [])
 compileExp     g (AppV {t = Wrd} x [])       = return (Var (lookup x g) , [])
 compileExp     g (AppV {t = Bol} x [])       = return (Var (lookup x g) , [])
 compileExp     g (AppV {t = Flt} x [])       = return (Var (lookup x g) , [])
 compileExp     g (AppV {t = (Tpl _ _)} x []) = return (Var (lookup x g) , [])
 compileExp     g (AppV {t = (Ary _)} x [])   = return (Var (lookup x g) , [])
 compileExp     g (AppV {t = Cmx} x [])       = return (Var (lookup x g) , [])
 compileExp     g (AppV {t = (Arr _ _)} x lss@(_ :: _))
                              = do (es , ss) <- compileEnv g lss
                                   return (App (lookup x g) es, ss)
 compileExp {a} g (Cnd l m n) = do (el , sl) <- compileExp g l
                                   (em , sm) <- compileExp g m
                                   (en , sn) <- compileExp g n
                                   v <- newVar a
                                   return (Var v,
                                           sl ++
                                           [If el
                                              (sm ++ [Assign v em])
                                              (sn ++ [Assign v en])])
 compileExp {a} g (Whl l m n) = do v <- newVar a
                                   (el , sl) <- compileExp (v :: g) l
                                   (em , sm) <- compileExp (v :: g) m
                                   (en , sn) <- compileExp       g  n
                                   return (Var v,
                                           sn ++
                                           [Assign v en] ++
                                           sl ++
                                           [Whl el
                                              (sm ++
                                               [Assign v em] ++
                                               sl)])
 compileExp {a=Tpl b c} g (Tpl l m)
                           = do (el , sl) <- compileExp g l
                                (em , sm) <- compileExp g m
                                return (App "newTpl"
                                         [Var (show (printType b) ++ show (printType c)), el, em],
                                        sl ++ sm)
 compileExp g (Fst l)         = do (el , sl) <- compileExp g l
                                   return (App "fst" [el] , sl)
 compileExp g (Snd l)         = do (el , sl) <- compileExp g l
                                   return (App "snd" [el] , sl)
 compileExp {a=Ary b} g (Ary l f)
                           = do xl <- newVar Wrd
                                xa <- newVar b
                                xi <- newVar Wrd
                                (el , sl) <- compileExp        g  l
                                (ef , sf) <- compileExp (xi :: g) f
                                return (Var xa,
                                        sl ++
                                        [Assign xl el,
                                         Assign xa (App "newAry"
                                           [Var (show (printType b)), Var xl]),
                                         Assign xi (Wrd 0),
                                         Whl (App "ltd" [Var xi, Var xl])
                                           (sf ++
                                            [Assign xa
                                              (App "setAry" [Var xa, Var xi, ef]),
                                             Assign xi
                                               (App "add" [Var xi, Wrd 1])])])
 compileExp g (Len l)         = do (el  , sl) <- compileExp g l
                                   return (App "len" [el] , sl)
 compileExp g (Ind l m)       = do (el , sl) <- compileExp g l
                                   (em , sm) <- compileExp g m
                                   return (App "ind" [el , em], sl ++ sm)
 compileExp g (Let {a} l f)   = do xl <- newVar a
                                   (el , sl) <- compileExp        g  l
                                   (ef , sf) <- compileExp (xl :: g) f
                                   return (ef,
                                           sl ++
                                           [Assign xl el] ++
                                           sf)
 compileExp g (Cmx l m)       = do (el , sl) <- compileExp g l
                                   (em , sm) <- compileExp g m
                                   return (App "cmx" [el , em], sl ++ sm)
 compileExp g (Tag x l)       = compileExp g l
 compileExp g (Mul l m)       = do (el , sl) <- compileExp g l
                                   (em , sm) <- compileExp g m
                                   return (App "mul" [el , em], sl ++ sm)
 compileExp g (Add l m)       = do (el , sl) <- compileExp g l
                                   (em , sm) <- compileExp g m
                                   return (App "add" [el , em], sl ++ sm)
 compileExp g (Sub l m)       = do (el , sl) <- compileExp g l
                                   (em , sm) <- compileExp g m
                                   return (App "sub" [el , em], sl ++ sm)
 compileExp g (Eql l m)       = do (el , sl) <- compileExp g l
                                   (em , sm) <- compileExp g m
                                   return (App "eql" [el , em], sl ++ sm)
 compileExp g (Ltd l m)       = do (el , sl) <- compileExp g l
                                   (em , sm) <- compileExp g m
                                   return (App "ltd" [el , em], sl ++ sm)
 compileExp g (Mem l)         = compileExp g l

-- compiles terms with free variables (not the primitives, i.e. the ones captured by
-- provided the environment) by considering the free variable as the function
-- supplied parameter
compileFun : All (const String) g -> Exp (a :: g) b -> CompileMonad (C.Exp , List Stmt)
compileFun {a} g f = do v <- newParam a
                        compileExp (v :: g) f

-- runs the CompileMoand by adding the list of parameters to a function header, and
--  declaring local variables before its body.
runCompileMonad : Typ -> CompileMonad (Exp , List Stmt) -> String -> Int -> C.FunC
runCompileMonad t m n i = let ((exp , stmts) , (_ , ps , vs)) = runState m (i , [] , [])
                          in  MkFunC t n ps
                                (map Declare vs ++
                                 stmts ++
                                 [Return exp])

-- collects types of all the subterms
-- (I hoped there would have been some generic / meta- programming facility there to help)
collectTypesExp : {a : Typ} -> Exp g a -> List Typ
collectTypesExp {a = Wrd}       (ConI x)    = [Wrd]
collectTypesExp {a = Bol}       (ConB x)    = [Bol]
collectTypesExp {a = Flt}       (ConF x)    = [Flt]
collectTypesExp {a = (out t)}   (AppV _ xs) = (out t) :: foldAll (\ _, ts, x  => ts ++ collectTypesExp x) [] xs
collectTypesExp {a = a}         (Cnd l m n) = a       :: collectTypesExp l ++ collectTypesExp m ++ collectTypesExp n
collectTypesExp {a = a}         (Whl l m n) = a       :: collectTypesExp l ++ collectTypesExp m ++ collectTypesExp n
collectTypesExp {a = (Tpl t b)} (Tpl l m)   = Tpl t b :: collectTypesExp l ++ collectTypesExp m
collectTypesExp {a = a}         (Fst l)     = a       :: collectTypesExp l
collectTypesExp {a = a}         (Snd l)     = a       :: collectTypesExp l
collectTypesExp {a = (Ary t)}   (Ary l m)   = Ary t   :: collectTypesExp l ++ collectTypesExp m
collectTypesExp {a = Wrd}       (Len l)     = Wrd     :: collectTypesExp l
collectTypesExp {a = a}         (Ind l m)   = a       :: collectTypesExp l ++ collectTypesExp m
collectTypesExp {a = a}         (Let l m)   = a       :: collectTypesExp l ++ collectTypesExp m
collectTypesExp {a = Cmx}       (Cmx l m)   = Cmx     :: collectTypesExp l ++ collectTypesExp m
collectTypesExp {a = a}         (Tag x l)   = a       :: collectTypesExp l
collectTypesExp {a = a}         (Mul l m)   = a       :: collectTypesExp l ++ collectTypesExp m
collectTypesExp {a = a}         (Add l m)   = a       :: collectTypesExp l ++ collectTypesExp m
collectTypesExp {a = a}         (Sub l m)   = a       :: collectTypesExp l ++ collectTypesExp m
collectTypesExp {a = Bol}       (Eql l m)   = Bol     :: collectTypesExp l ++ collectTypesExp m
collectTypesExp {a = Bol}       (Ltd l m)   = Bol     :: collectTypesExp l ++ collectTypesExp m
collectTypesExp {a = a}         (Mem l)     = a       :: collectTypesExp l

-- Generates C structs for each instantiation of polymorphic datatypes
genStructs : List Typ -> String
genStructs ts = concat (
                ["typedef struct {Wrd size; "++s++"* elems;} Ary"++s++";\n"
                | Ary a <- ts,
                  a /= Wrd,
                  let s = show (printType a)] ++
                ["typedef struct {"++sa++" fst; "++sb++" snd;} Tpl"++sa++sb++";\n"
                | Tpl a b <- ts,
                let sa = show (printType a),
                let sb = show (printType b)])

-- Type classes to provide uniform access to the compile functions

class TypeCollectable a where
  collectTypes : a -> List Typ

instance TypeCollectable (Exp g c) where
  collectTypes = collectTypesExp

class Compilable a where
  compileTerm : a -> CompileMonad (C.Exp , List Stmt)

instance Compilable (All (const String) g , Exp g b) where
  compileTerm (g , e) = compileExp g e

instance Compilable (All (const String) g , Exp (a :: g) b) where
  compileTerm (g , e) = compileFun g e

-- the main function used for compiling terms using the given
-- typing signature of the language primitives
compileWith : (Compilable (All (const String) g , a), TypeCollectable a) =>
              All (const String) g -> Typ -> a -> String
compileWith g t e = let c = runCompileMonad t (compileTerm (g , e)) "prog" 0
                    in  "#include \"header.h\"\n\n" ++
                        genStructs (nub (collectTypes e)) ++ "\n" ++
                         (show . printFunC) c

ex1 : Exp [Flt] Flt
ex1 = Whl (Ltd (AppV Zro Nil) (ConF 20.0))
          (Add (AppV Zro Nil) (ConF 1.0))
          (AppV Zro Nil)

c1 : String
c1 = compileWith Nil Flt ex1
