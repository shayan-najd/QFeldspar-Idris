module Pretty

data Doc = Empty
         | Charr Char             -- invariant: char is not '\n'
         | Text Integer String      -- invariant: text doesn't contain '\n'
         | Line Bool            -- True <=> when undone by group, do not insert a space
         | Cat Doc Doc
         | Nest Integer Doc

infixr 5 </>,<//>,<$$>
infixr 6 <>

beside : Doc -> Doc -> Doc
beside x y      = Cat x y

text : String -> Doc
text "" = Empty
text s  = Text (toIntegerNat $ length s) s

line : Doc
line = Line False

linebreak : Doc
linebreak = Line True

char : Char -> Doc
char '\n' = line
char c    = Charr c

-- | The document @semi@ contains a semi colon, \";\".
semi : Doc
semi = char ';'

-- | The document @comma@ contains a comma, \",\".
comma : Doc
comma = char ','

-- | The document @space@ contains a single space, \" \".
--
-- > x <+> y   = x <> space <> y
space : Doc
space = char ' '

-- | The document @lbrace@ contains a left brace, \"{\".
lbrace : Doc
lbrace = char '{'

-- | The document @rbrace@ contains a right brace, \"}\".
rbrace : Doc
rbrace = char '}'

-- | The document @lparen@ contains a left parenthesis, \"(\".
lparen : Doc
lparen = char '('

-- | The document @rparen@ contains a right parenthesis, \")\".
rparen : Doc
rparen = char ')'

-- | The document @(nest i x)@ renders document @x@ with the current
-- indentation level increased by i (See also 'hang', 'align' and
-- 'indent').
--
-- > nest 2 (text "hello" <$> text "world") <$> text "!"
--
-- outputs as:
--
-- @
-- hello
--   world
-- !
-- @
nest : Integer -> Doc -> Doc
nest i x = Nest i x


-- | The document @(x \<\> y)@ concatenates document @x@ and document
-- @y@. It is an associative operation having 'empty' as a left and
-- right unit.  (infixr 6)
(<>) : Doc -> Doc -> Doc
x <> y = x `beside` y

-- | The document @(x \<+\> y)@ concatenates document @x@ and @y@ with a
-- @space@ in between.  (infixr 6)
(<+>) : Doc -> Doc -> Doc
x <+> y = x <> space <> y

fold : (Doc -> Doc -> Doc) -> List Doc -> Doc
fold f []       = Empty
fold f ds       = foldr1 f ds

(<$$>) : Doc -> Doc -> Doc
x <$$> y = x <> linebreak <> y

-- | The document @(vcat xs)@ concatenates all documents @xs@
-- vertically with @(\<$$\>)@. If a 'group' undoes the line breaks
-- inserted by @vcat@, all documents are directly concatenated.
vcat : List Doc -> Doc
vcat = fold (<$$>)

-- | The document @(enclose l r x)@ encloses document @x@ between
-- documents @l@ and @r@ using @(\<\>)@.
--
-- > enclose l r x   = l <> x <> r
enclose : Doc -> Doc -> Doc -> Doc
enclose l r x = l <> x <> r

-- | Document @(parens x)@ encloses document @x@ in parenthesis, \"(\"
-- and \")\".
parens : Doc -> Doc
parens = enclose lparen rparen

data SimpleDoc  = SEmpty
               | SChar Char SimpleDoc
               | SText Integer String SimpleDoc
               | SLine Integer SimpleDoc

data Docs = Nil
          | Cons Integer Doc Docs

toFloat : Nat -> Float
toFloat = fromInteger . toIntegerNat

round : Float -> Nat
round = fromInteger . prim__fromFloatBigInt


renderPretty : Float -> Nat -> Doc -> SimpleDoc
renderPretty rfrac w x
   = best 0 0 (Cons 0 x Nil)
   where
     -- r :: the ribbon width in characters
     r : Nat
     r  = max 0 (min w (round ((toFloat w) * rfrac)))

     -- best :: n = indentation of current line
     --         k = current column
     --        (ie. (k >= n) && (k - n == count of inserted characters)

     best n k Nil      = SEmpty
     best n k (Cons i d ds)
       = case d of
           Empty       => best n k ds
           Charr c     => let k' = k+1 in SChar c (best n k' ds)
           Text l s    => let k' = k+l in SText l s (best n k' ds)
           Line _      => SLine i (best i i ds)
           Cat x y     => best n k (Cons i x (Cons i y ds))
           Nest j x    => let i' = i+j in best n k (Cons i' x ds)

spaces : Integer -> String
spaces n = if n <= 0
           then  ""
           else pack (replicate (fromInteger n) ' ')

displayS : SimpleDoc -> String -> String
displayS SEmpty             = id
displayS (SChar c x)        = (strCons c) . displayS x
displayS (SText l s x)      = (s ++) . displayS x
displayS (SLine i x)        = ((strCons '\n' (spaces i)) ++) . displayS x

instance Show Doc where
 show doc = displayS (renderPretty 0.4 80 doc) ""
