module Types

import Data.Complex

data Array a = mkArray Bits32 (Bits32 -> a)
-- data Vector a = MkVector Bits32 (Bits32 -> a)

data Typ : Type where
  Wrd : Typ
  Bol : Typ
  Flt : Typ
  Arr : Typ -> Typ -> Typ
  Tpl : Typ -> Typ -> Typ
  Ary : Typ -> Typ
--  Vct : Typ -> Typ
--  May : Typ -> Typ
  Cmx : Typ

%name Typ t,t'

getType : Typ -> Type
getType Wrd       = Bits32
getType Bol       = Bool
getType Flt       = Float
getType (Arr x y) = getType x -> getType y
getType (Tpl x y) = (getType x , getType y)
getType (Ary x)   = Array (getType x)
-- getType (Vct x)   = Vector (getType x)
-- getType (May x)   = Maybe (getType x)
getType Cmx       = Complex Float

args : Typ -> List Typ
args (Arr x y) = x :: args y
args _         = []

out : Typ -> Typ
out (Arr x y) = out y
out x         = x

namespace Arith
 data Arith : Typ -> Type where
   Wrd : Arith Wrd
   Flt : Arith Flt
   Cmx : Arith Cmx

namespace Eq
 data Eq : Typ -> Type where
   Wrd : Eq Wrd
   Flt : Eq Flt
   Cmx : Eq Cmx
   Bol : Eq Bol

namespace Ord
 data Ord : Typ -> Type where
   Wrd : Ord Wrd
   Flt : Ord Flt
   Bol : Ord Bol
