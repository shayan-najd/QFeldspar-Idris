import MiniFeldspar

ex1 : Float
ex1 = eval [] (Cnd True 1.1 42.0)

{-
boolElim : Exp g Bol -> Lazy $ Exp g a -> Lazy $ Exp g a -> Lazy $ Exp g a
boolElim l m n = Cnd l m n

ex2 : Float
ex2 = eval [] (if ConB True then ConF 1.1 else ConF 42.0)
-}

ex2 : Float
ex2 = eval [] (Cnd True 1.1 42.0)

ex3 : Exp [Flt] Flt
ex3 = Whl (Ltd (AppV Zro []) 20.0)
          ((AppV Zro []) + 1.0)
          (AppV Zro [])

c3 : String
c3 = compileWith [] Flt ex3
