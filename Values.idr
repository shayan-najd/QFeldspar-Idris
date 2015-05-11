module Values

import All
import Types
import Data.Complex

conI : Bits32 -> Bits32
conI = id

conF : Float -> Float
conF = id

conB : Bool -> Bool
conB = id

appV : getType a -> All getType (args a) -> getType (out a)
appV {a = Arr t t'}   f (x :: y) = appV (f x) y
appV {a = Wrd}        f []       = f
appV {a = Bol}        f []       = f
appV {a = Flt}        f []       = f
appV {a = Tpl t t'}   f []       = f
appV {a = Ary t}      f []       = f
appV {a = Cmx}        f []       = f

cnd : Bool -> a -> a -> a
cnd b t f = if b then t else f

whl : (a -> Bool) -> (a -> a) -> a -> a
whl c b i = if c i then whl c b (b i) else i

tpl : a -> b -> (a , b)
tpl x y = (x , y)

ary : Bits32 -> (Bits32 -> a) -> Array a
ary = mkArray

len : Array a -> Bits32
len (mkArray x _ ) = x

ind : Array a -> Bits32 -> a
ind (mkArray _ f) i = f i

lett : a -> (a -> b) -> b
lett x f = f x

cmx : Float -> Float -> Complex Float
cmx = (:+)

tag : a -> b -> b
tag _ = id

mul : {auto isArith : Arith a} -> getType a -> getType a -> getType a
mul {isArith = Wrd} = (*)
mul {isArith = Flt} = (*)
mul {isArith = Cmx} = (*)

add : {auto isArith : Arith a} -> getType a -> getType a -> getType a
add {isArith = Wrd} = (+)
add {isArith = Flt} = (+)
add {isArith = Cmx} = (+)

sub : {auto isArith : Arith a} -> getType a -> getType a -> getType a
sub {isArith = Wrd} = (-)
sub {isArith = Flt} = (-)
sub {isArith = Cmx} = (-)

eql : {auto isEq : Eq.Eq a} -> getType a -> getType a -> Bool
eql {isEq = Wrd} = (==)
eql {isEq = Flt} = (==)
eql {isEq = Cmx} = (==)
eql {isEq = Bol} = (==)

ltd : {auto isOrd : Ord.Ord a} -> getType a -> getType a -> Bool
ltd {isOrd = Wrd} = (<)
ltd {isOrd = Flt} = (<)
ltd {isOrd = Bol} = (<)

mem : a -> a
mem = id
