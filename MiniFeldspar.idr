module MiniFeldspar

import public Expressions
import public Types
import public All
import public Data.Complex
import public Evaluation
import public Compilation

Prelude : List Typ
Prelude = [Cmx `Arr` Flt,
           Cmx `Arr` Flt,
           Wrd `Arr` (Wrd `Arr` Wrd),
           Flt `Arr` (Flt `Arr` Flt),
           Wrd `Arr` (Wrd `Arr` Wrd),
           Wrd `Arr` (Wrd `Arr` Wrd),
           Wrd `Arr` (Wrd `Arr` Wrd),
           Wrd `Arr` (Wrd `Arr` Wrd),
           Wrd `Arr` (Wrd `Arr` Wrd),
           Wrd `Arr` Wrd,
           Wrd `Arr` Flt,
           Flt `Arr` Cmx,
           Wrd `Arr` Wrd,
           Flt `Arr` Flt,
           Ary Wrd]

Dp : Typ -> Type
Dp = Exp Prelude

{-
trmEql ::  HasSin TFG.Typ a => Dp a -> Dp a -> MP.Bool
trmEql  = FMWS.eql

trmEqlF :: (HasSin TFG.Typ a , HasSin TFG.Typ b) =>
           (Dp a -> Dp b) -> (Dp a -> Dp b) -> MP.Bool
trmEqlF = FMWS.eqlF
-}

implicit
conF : Float -> Exp g Flt
conF = ConF

{-
class Type (InT a) => Syn a where
  type InT a :: *
  toExp  :: a -> Dp (InT a)
  frmExp :: Dp (InT a) -> a

instance Type a => Syn (Dp a) where
  type InT (Dp a) = a
  toExp  x = x
  frmExp x = x

toExpF :: (Syn a , Syn b) => (a -> b) -> Dp (InT a) -> Dp (InT b)
toExpF f = toExp . f . frmExp

frmExpF f = frmExp . f . toExp
-}

True : Exp g Bol
True = ConB True

False : Exp g Bol
False = ConB False

{-
(?) :: Syn a => Dp Bol -> (a , a) -> a
c ? (t , e) = frmExp (Cnd c (toExp t) (toExp e))

while :: Syn a => (a -> Dp Bol) -> (a -> a) -> a -> a
while c b i = frmExp (Whl (toExpF c) (toExpF b) (toExp i))

instance (Syn a , Syn b) => Syn (a , b) where
    type InT (a , b) = (InT a , InT b)
    toExp (x , y)    = Tpl (toExp x) (toExp y)
    frmExp ee        = let e = $shared ee in
                       (frmExp (Fst e) , frmExp (Snd e))
-}

--mkArr :: Dp Wrd -> (Dp Wrd -> Dp t) -> Dp (Ary t)
--mkArr = Ary

lnArr  : Exp g (Ary a) -> Exp g Wrd
lnArr = Len

ixArr : Exp g (Ary a) -> Exp g Wrd -> Exp g a
ixArr = Ind

data Vec' t = MkVec (Dp Wrd) (Dp Wrd -> t)

{-
instance Syn a => Syn (Vec' a) where
  type InT (MkVec' a)  = Ary (InT a)
  toExp  (MkVec' l f)  = Ary l (\ i -> toExp (f i))
  frmExp aa         = let a = $shared aa in
                      MkVec (Len a) (\ i -> frmExp (Ind a i))
-}

-- What are pattern synonyms in Idris
-- pattern x :+. y = Cmx x y

save : Exp g a -> Exp g a
save = Mem

{-
class Syn a => Undef a where
  undef :: a

instance Undef (Dp Bol) where
  undef = FalseE

instance Undef (Dp Wrd) where
  undef = 0

instance Undef (Dp Float) where
  undef = 0

instance (Undef a, Undef b) => Undef (a,b) where
  undef = (undef, undef)

data Opt_R a = Opt_R { def :: Dp Bol, val :: a }

instance Syn a => Syn (Opt_R a) where
  type InT (Opt_R a) =  (Bol, InT a)
  toExp (Opt_R b x)  =  Tpl b (toExp x)
  frmExp pp          =  let p = $shared pp in
                        Opt_R (Fst p) (frmExp (Snd p))

some_R            ::  a -> Opt_R a
some_R x          =   Opt_R TrueE x

none_R            ::  Undef a => Opt_R a
none_R            =   Opt_R FalseE undef

option_R          ::  Syn b => b -> (a -> b) -> Opt_R a -> b
option_R d f o    =   def o ? (f (val o), d)

newtype Opt a = O { unO :: forall b . Undef b =>
                           ((a -> Opt_R b) -> Opt_R b) }

instance Monad Opt where
  return x    =  O (\g -> g x)
  m >>= k     =  O (\g -> unO m (\x -> unO (k x) g))

instance Undef a => Syn (Opt a) where
  type InT (Opt a) =  (Bol, InT a)
  frmExp           =  lift . frmExp
  toExp            =  toExp . lower

lift          ::  Opt_R a -> Opt a
lift o        =   O (\g -> Opt_R  (def o ? (def (g (val o)), FalseE))
                                  (def o ? (val (g (val o)), undef)))

lower         ::  Undef a => Opt a -> Opt_R a
lower m       =   unO m some_R

some          ::  a -> Opt a
some a        =   lift (some_R a)

none          ::  Undef a => Opt a
none          =   lift none_R

option        ::  (Undef a, Undef b) => b -> (a -> b) -> Opt a -> b
option d f o  =   option_R d f (lower o)
-}

instance Num (Exp g Flt) where
  (+) = Add
  (-) = Sub
  (*) = Mul
  fromInteger x = ConF (fromInteger x)
  abs = Abs

instance Num (Exp g Wrd) where
  (+) = Add
  (-) = Sub
  (*) = Mul
  fromInteger x = ConI (fromInteger x)
  abs = Abs

instance Num (Exp g Cmx) where
  (+) = Add
  (-) = Sub
  (*) = Mul
  fromInteger x = Cmx (ConF (fromInteger x)) (ConF 0.0)
  abs = Abs

infix 4 ==.
class EqE a where
  (==.) : a -> a -> Dp Bol

instance EqE (Dp Bol) where
  (==.) = Eql

instance EqE (Dp Wrd) where
  (==.) = Eql

instance EqE (Dp Flt) where
  (==.) = Eql

instance EqE (Dp Cmx) where
  (==.) = Eql

infix 4 <.
class OrdE a where
  (<.) : a -> a -> Dp Bol

instance OrdE (Dp Bol) where
  (<.) = Ltd

instance OrdE (Dp Wrd) where
  (<.) = Ltd

instance OrdE (Dp Flt) where
  (<.) = Ltd

{-
share :: (Syn tl , Syn tb) =>
         tl -> (tl -> tb) -> tb
share e f = frmExp (Let (toExp e) (toExp . f . frmExp))
-}

realPart : Dp Cmx -> Dp Flt
realPart e = AppV Zro [e]

imagPart : Dp (Cmx) -> Dp Flt
imagPart e = AppV (Suc Zro) [e]

div : Dp Wrd -> Dp Wrd -> Dp Wrd
div e1 e2 = AppV (Suc $ Suc Zro) [e1,e2]

-- Different From Haskell
-- infixl 7 /
(/) : Dp Flt -> Dp Flt -> Dp Flt
e1 / e2 = AppV (Suc $ Suc $ Suc Zro) [e1,e2]

-- no fromRational in Idris

infixl 7 .&.
(.&.) : Dp Wrd -> Dp Wrd -> Dp Wrd
e1 .&. e2 = AppV (Suc $ Suc $ Suc $ Suc Zro) [e1,e2]

infixl 7 .|.
(.|.)  : Dp Wrd -> Dp Wrd -> Dp Wrd
e1 .|. e2 = AppV (Suc $ Suc $ Suc $ Suc $ Suc Zro) [e1,e2]

xor : Dp Wrd -> Dp Wrd -> Dp Wrd
xor e1 e2 = AppV (Suc $ Suc $ Suc $ Suc $ Suc $ Suc Zro) [e1,e2]

shfRgt : Dp Wrd -> Dp Wrd -> Dp Wrd
shfRgt e1 e2 = AppV (Suc $ Suc $ Suc $ Suc $ Suc $ Suc $ Suc Zro) [e1,e2]

shfLft : Dp Wrd -> Dp Wrd -> Dp Wrd
shfLft e1 e2 = AppV (Suc $ Suc $ Suc $ Suc $ Suc $ Suc $ Suc $ Suc Zro) [e1,e2]

complement : Dp Wrd -> Dp Wrd
complement e = AppV (Suc $ Suc $ Suc $ Suc $ Suc $ Suc $ Suc $ Suc $ Suc Zro) [e]

i2f : Dp Wrd -> Dp Flt
i2f e = AppV (Suc $ Suc $ Suc $ Suc $ Suc $ Suc $ Suc $ Suc $ Suc $ Suc Zro) [e]

cis : Dp Flt -> Dp Cmx
cis e = AppV (Suc $ Suc $ Suc $ Suc $ Suc $ Suc $ Suc $ Suc $ Suc $ Suc $ Suc Zro) [e]

ilog2 : Dp Wrd -> Dp Wrd
ilog2 e = AppV (Suc $ Suc $ Suc $ Suc $ Suc $ Suc $ Suc $ Suc $ Suc $ Suc $ Suc $ Suc Zro) [e]

sqrt : Dp Flt -> Dp Flt
sqrt e = AppV (Suc $ Suc $ Suc $ Suc $ Suc $ Suc $ Suc $ Suc $ Suc $ Suc $ Suc $ Suc $ Suc Zro) [e]

hashTable : Dp (Ary Wrd)
hashTable = AppV (Suc $ Suc $ Suc $ Suc $ Suc $ Suc $ Suc $ Suc $ Suc $ Suc $ Suc $ Suc $ Suc $ Suc Zro) []
