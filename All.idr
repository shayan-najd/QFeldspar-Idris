module All
import Types

data All : (k -> Type) -> List k -> Type where
  Nil  : All p []
  (::) : p x -> All p xs -> All p (x :: xs)

map : ({a : k} -> p a -> p' a) -> All p xs -> All p' xs
map _ []       = []
map f (y :: z) = f y :: map f z

-- Couldn't write it with {b : Typ}
foldAll : ((b : Typ) -> a -> p b -> a) -> a -> All p g -> a
foldAll {g = []}        _ i []        = i
foldAll {g = (a :: _)} f i (x :: xs) = f a (foldAll f i xs) x

data Var' : List a -> a -> Type where
  Zro : Var' (a :: g) a
  Suc : Var' g a -> Var' (b :: g) a

lookup : Var' g a -> All p g -> p a
lookup Zro     (z :: w) = z
lookup (Suc x) (z :: w) = lookup x w
