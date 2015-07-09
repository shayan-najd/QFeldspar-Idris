import MiniFeldspar
import Expressions
import Types
import All

ipgray : Exp (Ary Wrd :: Prelude) (Ary Wrd)
ipgray = Ary (AppV (Suc $ Suc $ Suc Zro) [Len (AppV Zro []) , ConI 3])
             (AppV (Suc $ Suc $ Suc $ Suc Zro)
                [((Ind (AppV (Suc Zro) [])  (((AppV Zro []) * (ConI 3)))) * 30) +
                 ((Ind (AppV (Suc Zro) [])  (((AppV Zro []) * (ConI 3))+1)) * 59) +
                 ((Ind (AppV (Suc Zro) [])  (((AppV Zro []) * (ConI 3))+2)) * 11)
                , 100])

-- compile below with
--   "gcc -o {name} {name}.c -lm -std=c99
-- where {name} is the name of the file containing below string
ipgrayC : String
ipgrayC = makeIP (compileWith prelude (Ary Wrd) ipgray)
