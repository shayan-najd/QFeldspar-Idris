import MiniFeldspar
import Expressions
import Types
import All

redCoefficient : Dp Wrd
redCoefficient   = 30

greenCoefficient : Dp Wrd
greenCoefficient = 59

blueCoefficient : Dp Wrd
blueCoefficient  = 11

rgbToGray : Dp Wrd -> Dp Wrd -> Dp Wrd -> Dp Wrd
rgbToGray r g b =
            divE
            ((r * redCoefficient)   +
             (g * greenCoefficient) +
             (b * blueCoefficient)) 100

{-
ipgrayVec :: Vec (Dp Wrd) -> Vec (Dp Wrd)
ipgrayVec = \ (Vec l f) ->
            Vec (divE l 3)
                 (\ i -> share (i * 3) (\ j ->
                         rgbToGray
                         (f j)
                         (f (j + 1))
                         (f (j + 2))))

ipgray :: Dp (Ary Wrd) -> Dp (Ary Wrd)
ipgray = toExpF ipgrayVec
-}
{-
ipgray : Dp (Ary Wrd) -> Dp (Ary Wrd)
ipgray a = Ary (divE (lnArr a) 3)
               (let i = AppV Zro []
                    j = i * 3
                    f = ixArr a
                in rgbToGray
                   (f j)
                   (f (j + 1))
                   (f (j + 2)))
-}
