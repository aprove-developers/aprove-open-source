module Prelude (
--  module PreludeList,
    map, (++), concat, filter,
    head, last, tail, init, null, length, (!!),
    foldl, foldl1, scanl, scanl1, foldr, foldr1, scanr, scanr1,
    iterate, repeat, replicate, cycle,
    take, drop, splitAt, takeWhile, dropWhile, span, break,
    lines, words, unlines, unwords, reverse, and, or,
    any, all, elem, notElem, lookup,
    sum, product, maximum, minimum, concatMap,
    zip, zip3, zipWith, zipWith3, unzip, unzip3,
--  module PreludeText,
    ReadS, ShowS,
    Read(readsPrec, readList),
    Show(show, showsPrec, showList),
    reads, shows, read, lex,
    showChar, showString, readParen, showParen,
--  module PreludeIO,
    FilePath, IOError, ioError, userError, catch,
    putChar, putStr, putStrLn, print,
    getChar, getLine, getContents, interact,
    readFile, writeFile, appendFile, readIO, readLn,
--  module Ix,
    Ix(range, index, inRange, rangeSize),
--  module Char,
    isAscii, isLatin1, isControl, isPrint, isSpace, isUpper, isLower,
    isAlpha, isDigit, isOctDigit, isHexDigit, isAlphaNum,
    digitToInt, intToDigit,
    toUpper, toLower,
    ord, chr,
    readLitChar, showLitChar, lexLitChar,
--  module Numeric
    showSigned, showInt,
    readSigned, readInt,
    readDec, readOct, readHex, readSigned,
    readFloat, lexDigits,
--  module Ratio,
    Ratio, Rational, (%), numerator, denominator, approxRational,
--  Non-standard exports
    IO(..),
    FunPtr, Ptr, Addr,
    Word, StablePtr, ForeignObj, ForeignPtr,
    Int8, Int16, Int32, Int64,
    Word8, Word16, Word32, Word64,

    Bool(False, True),
    Maybe(Nothing, Just),
    Either(Left, Right),
    Ordering(LT, EQ, GT),
    Char, String, Int, Integer, Float, Double, IO,
--  List type: []((:), [])
    (:),
--  Tuple types: (,), (,,), etc.
--  Trivial type: ()
--  Functions: (->)
    Rec, EmptyRec, EmptyRow, -- non-standard, should only be exported if TREX
    Eq((==), (/=)),
    Ord(compare, (<), (<=), (>=), (>), max, min),
    Enum(succ, pred, toEnum, fromEnum, enumFrom, enumFromThen,
         enumFromTo, enumFromThenTo),
    Bounded(minBound, maxBound),
--  Num((+), (-), (*), negate, abs, signum, fromInteger),
    Num((+), (-), (*), negate, abs, signum, fromInteger, fromInt),
    Real(toRational),
--  Integral(quot, rem, div, mod, quotRem, divMod, toInteger),
    Integral(quot, rem, div, mod, quotRem, divMod, even, odd, toInteger, toInt),
--  Fractional((/), recip, fromRational),
    Fractional((/), recip, fromRational, fromDouble),
    Floating(pi, exp, log, sqrt, (**), logBase, sin, cos, tan,
             asin, acos, atan, sinh, cosh, tanh, asinh, acosh, atanh),
    RealFrac(properFraction, truncate, round, ceiling, floor),
    RealFloat(floatRadix, floatDigits, floatRange, decodeFloat,
              encodeFloat, exponent, significand, scaleFloat, isNaN,
              isInfinite, isDenormalized, isIEEE, isNegativeZero, atan2),
    Monad((>>=), (>>), return, fail),
    Functor(fmap),
    mapM, mapM_, sequence, sequence_, (=<<),
    maybe, either,
    (&&), (||), not, otherwise,
    subtract, even, odd, gcd, lcm, (^), (^^),
    fromIntegral, realToFrac,
    fst, snd, curry, uncurry, id, const, (.), flip, ($), until,
    asTypeOf, error, undefined, 
    seq, ($!)
    ,terminator
  ) where

terminator = terminator
-- Standard value bindings {Prelude} ----------------------------------------

infixr 9  .
infixl 9  !!
infixr 8  ^, ^^, **
infixl 7  *, /, `quot`, `rem`, `div`, `mod`, :%, %
infixl 6  +, -
--infixr 5  :    -- this fixity declaration is hard-wired into Hugs
infixr 5  ++
infix  4  ==, /=, <, <=, >=, >, `elem`, `notElem`
infixr 3  &&
infixr 2  ||
infixl 1  >>, >>=
infixr 1  =<<
infixr 0  $, $!, `seq`

-- Equality and Ordered classes ---------------------------------------------

class Eq a where
    (==), (/=) :: a -> a -> Bool

    -- Minimal complete definition: (==) or (/=)
    x == y      = not (x/=y)
    x /= y      = not (x==y)

class (Eq a) => Ord a where
    compare                :: a -> a -> Ordering
    (<), (<=), (>=), (>)   :: a -> a -> Bool
    max, min               :: a -> a -> a

    -- Minimal complete definition: (<=) or compare
    -- using compare can be more efficient for complex types
    compare x y | x==y      = EQ
		| x<=y      = LT
		| otherwise = GT

    x <= y                  = compare x y /= GT
    x <  y                  = compare x y == LT
    x >= y                  = compare x y /= LT
    x >  y                  = compare x y == GT

    max x y   | x <= y      = y
	      | otherwise   = x
    min x y   | x <= y      = x
	      | otherwise   = y

class Bounded a where
    minBound, maxBound :: a
    -- Minimal complete definition: All

-- Numeric classes ----------------------------------------------------------

class (Eq a, Show a) => Num a where
    (+), (-), (*)  :: a -> a -> a
    negate         :: a -> a
    abs, signum    :: a -> a
    fromInteger    :: Integer -> a
    fromInt        :: Int -> a

    -- Minimal complete definition: All, except negate or (-)
    x - y           = x + negate y
    fromInt         = fromIntegral
    negate x        = 0 - x

class (Num a, Ord a) => Real a where
    toRational     :: a -> Rational

class (Real a, Enum a) => Integral a where
    quot, rem, div, mod :: a -> a -> a
    quotRem, divMod     :: a -> a -> (a,a)
    even, odd           :: a -> Bool
    toInteger           :: a -> Integer
    toInt               :: a -> Int

    -- Minimal complete definition: quotRem and toInteger
    n `quot` d           = q where (q,r) = quotRem n d
    n `rem` d            = r where (q,r) = quotRem n d
    n `div` d            = q where (q,r) = divMod n d
    n `mod` d            = r where (q,r) = divMod n d
    divMod n d           = if signum r == - signum d then (q-1, r+d) else qr
			   where qr@(q,r) = quotRem n d
    even n               = n `rem` 2 == 0
    odd                  = not . even
    toInt                = toInt . toInteger

class (Num a) => Fractional a where
    (/)          :: a -> a -> a
    recip        :: a -> a
    fromRational :: Rational -> a
    fromDouble   :: Double -> a

    -- Minimal complete definition: fromRational and ((/) or recip)
    recip x       = 1 / x
    fromDouble    = fromRational . toRational
    x / y         = x * recip y


class (Fractional a) => Floating a where
    pi                  :: a
    exp, log, sqrt      :: a -> a
    (**), logBase       :: a -> a -> a
    sin, cos, tan       :: a -> a
    asin, acos, atan    :: a -> a
    sinh, cosh, tanh    :: a -> a
    asinh, acosh, atanh :: a -> a

    -- Minimal complete definition: pi, exp, log, sin, cos, sinh, cosh,
    --				    asinh, acosh, atanh
    pi                   = 4 * atan 1
    x ** y               = exp (log x * y)
    logBase x y          = log y / log x
    sqrt x               = x ** 0.5
    tan x                = sin x / cos x
    sinh x               = (exp x - exp (-x)) / 2
    cosh x               = (exp x + exp (-x)) / 2
    tanh x               = sinh x / cosh x
    asinh x              = log (x + sqrt (x*x + 1))
    acosh x              = log (x + sqrt (x*x - 1))
    atanh x              = (log (1 + x) - log (1 - x)) / 2

class (Real a, Fractional a) => RealFrac a where
    properFraction   :: (Integral b) => a -> (b,a)
    truncate, round  :: (Integral b) => a -> b
    ceiling, floor   :: (Integral b) => a -> b

    -- Minimal complete definition: properFraction
    truncate x        = m where (m,_) = properFraction x

    round x           = let (n,r) = properFraction x
			    m     = if r < 0 then n - 1 else n + 1
			in case signum (abs r - 0.5) of
			    -1 -> n
			    0  -> if even n then n else m
			    1  -> m

    ceiling x         = if r > 0 then n + 1 else n
			where (n,r) = properFraction x

    floor x           = if r < 0 then n - 1 else n
			where (n,r) = properFraction x

class (RealFrac a, Floating a) => RealFloat a where
    floatRadix       :: a -> Integer
    floatDigits      :: a -> Int
    floatRange       :: a -> (Int,Int)
    decodeFloat      :: a -> (Integer,Int)
    encodeFloat      :: Integer -> Int -> a
    exponent         :: a -> Int
    significand      :: a -> a
    scaleFloat       :: Int -> a -> a
    isNaN, isInfinite, isDenormalized, isNegativeZero, isIEEE
		     :: a -> Bool
    atan2	     :: a -> a -> a

    -- Minimal complete definition: All, except exponent, signficand,
    --				    scaleFloat, atan2
    exponent x        = if m==0 then 0 else n + floatDigits x
			where (m,n) = decodeFloat x
    significand x     = encodeFloat m (- floatDigits x)
			where (m,_) = decodeFloat x
    scaleFloat k x    = encodeFloat m (n+k)
			where (m,n) = decodeFloat x
    atan2 y x
      | x>0           = atan (y/x)
      | x==0 && y>0   = pi/2
      | x<0 && y>0    = pi + atan (y/x)
      | (x<=0 && y<0) ||
        (x<0 && isNegativeZero y) ||
        (isNegativeZero x && isNegativeZero y)
		      = - atan2 (-y) x
      | y==0 && (x<0 || isNegativeZero x)
		      = pi    -- must be after the previous test on zero y
      | x==0 && y==0  = y     -- must be after the other double zero tests
      | otherwise     = x + y -- x or y is a NaN, return a NaN (via +)

-- Numeric functions --------------------------------------------------------

subtract       :: Num a => a -> a -> a
subtract        = flip (-)

gcd            :: Integral a => a -> a -> a
gcd 0 0         = error "" -- error "Prelude.gcd: gcd 0 0 is undefined"
gcd x y         = gcd' (abs x) (abs y)
		  where gcd' x 0 = x
			gcd' x y = gcd' y (x `rem` y)

lcm            :: (Integral a) => a -> a -> a
lcm _ 0         = 0
lcm 0 _         = 0
lcm x y         = abs ((x `quot` gcd x y) * y)

(^)            :: (Num a, Integral b) => a -> b -> a
x ^ 0           = 1
x ^ n  | n > 0  = f x (n-1) x
		  where f _ 0 y = y
			f x n y = g x n where
				  g x n | even n    = g (x*x) (n`quot`2)
					| otherwise = f x (n-1) (x*y)
_ ^ _           = error "" -- error "Prelude.^: negative exponent"

(^^)           :: (Fractional a, Integral b) => a -> b -> a
x ^^ n          = if n >= 0 then x ^ n else recip (x^(-n))

fromIntegral   :: (Integral a, Num b) => a -> b
fromIntegral    = fromInteger . toInteger

realToFrac     :: (Real a, Fractional b) => a -> b
realToFrac      = fromRational . toRational

-- Index and Enumeration classes --------------------------------------------

class (Ord a) => Ix a where
    range                :: (a,a) -> [a]
    index                :: (a,a) -> a -> Int
    inRange              :: (a,a) -> a -> Bool
    rangeSize            :: (a,a) -> Int

    rangeSize r@(l,u)
             | null (range r) = 0
             | otherwise      = index r u + 1
	-- NB: replacing "null (range r)" by  "not (l <= u)"
	-- fails if the bounds are tuples.  For example,
	-- 	(1,2) <= (2,1)
	-- but the range is nevertheless empty
	--	range ((1,2),(2,1)) = []

class Enum a where
    succ, pred           :: a -> a
    toEnum               :: Int -> a
    fromEnum             :: a -> Int
    enumFrom             :: a -> [a]              -- [n..]
    enumFromThen         :: a -> a -> [a]         -- [n,m..]
    enumFromTo           :: a -> a -> [a]         -- [n..m]
    enumFromThenTo       :: a -> a -> a -> [a]    -- [n,n'..m]

    -- Minimal complete definition: toEnum, fromEnum
    succ                  = toEnum . (1+)       . fromEnum
    pred                  = toEnum . subtract 1 . fromEnum
    enumFrom x            = map toEnum [ fromEnum x ..]
    enumFromTo x y        = map toEnum [ fromEnum x .. fromEnum y ]
    enumFromThen x y      = map toEnum [ fromEnum x, fromEnum y ..]
    enumFromThenTo x y z  = map toEnum [ fromEnum x, fromEnum y .. fromEnum z ]

-- Read and Show classes ------------------------------------------------------

type ReadS a = String -> [(a,String)]
type ShowS   = String -> String

class Read a where
    readsPrec :: Int -> ReadS a
    readList  :: ReadS [a]

    -- Minimal complete definition: readsPrec
    readList   = readParen False (\r -> [pr | ("[",s) <- lex r,
					      pr      <- readl s ])
		 where readl  s = [([],t)   | ("]",t) <- lex s] ++
				  [(x:xs,u) | (x,t)   <- reads s,
					      (xs,u)  <- readl' t]
		       readl' s = [([],t)   | ("]",t) <- lex s] ++
				  [(x:xs,v) | (",",t) <- lex s,
					      (x,u)   <- reads t,
					      (xs,v)  <- readl' u]

class Show a where
    show      :: a -> String
    showsPrec :: Int -> a -> ShowS
    showList  :: [a] -> ShowS

    -- Minimal complete definition: show or showsPrec
    show x          = showsPrec 0 x ""
    showsPrec _ x s = show x ++ s
    showList []     = showString "[]"
    showList (x:xs) = showChar '[' . shows x . showl xs
		      where showl []     = showChar ']'
			    showl (x:xs) = showChar ',' . shows x . showl xs

-- Monad classes ------------------------------------------------------------

class Functor f where
    fmap :: (a -> b) -> (f a -> f b)

class Monad m where
    return :: a -> m a
    (>>=)  :: m a -> (a -> m b) -> m b
    (>>)   :: m a -> m b -> m b
    fail   :: String -> m a

    -- Minimal complete definition: (>>=), return
    p >> q  = p >>= \ _ -> q
    fail s  = error s

sequence       :: Monad m => [m a] -> m [a]
sequence []     = return []
sequence (c:cs) = do x  <- c
		     xs <- sequence cs
		     return (x:xs)

sequence_        :: Monad m => [m a] -> m ()
sequence_         = foldr (>>) (return ())

mapM             :: Monad m => (a -> m b) -> [a] -> m [b]
mapM f            = sequence . map f

mapM_            :: Monad m => (a -> m b) -> [a] -> m ()
mapM_ f           = sequence_ . map f

(=<<)            :: Monad m => (a -> m b) -> m a -> m b
f =<< x           = x >>= f

-- Evaluation and strictness ------------------------------------------------

data WHNF a = WHNF !a

enforceWHNF :: (WHNF a) -> b -> b
enforceWHNF (WHNF x) y = y


seq           :: a -> b -> b
seq x y = enforceWHNF (WHNF x) y

($!) :: (a -> b) -> a -> b
f $! x                = x `seq` f x


-- Trivial type -------------------------------------------------------------

-- data () = () deriving (Eq, Ord, Ix, Enum, Read, Show, Bounded)

instance Eq () where
    () == ()  =  True

instance Ord () where
    compare () () = EQ

instance Ix () where
    range ((),())      = [()]
    index ((),()) ()   = 0
    inRange ((),()) () = True

instance Enum () where
    toEnum 0           = ()
    fromEnum ()        = 0
    enumFrom ()        = [()]
    --enumFromThen () () = repeat () --[()]
    --enumFromThenTo () () () = repeat ()

instance Read () where
    readsPrec p = readParen False (\r -> [((),t) | ("(",s) <- lex r,
						   (")",t) <- lex s ])

instance Show () where
    showsPrec p () = showString "()"

instance Bounded () where
    minBound = ()
    maxBound = ()

-- Boolean type -------------------------------------------------------------

--data Bool    = False | True
--	       deriving (Eq, Ord, Ix, Enum, Read, Show, Bounded)

(&&), (||)  :: Bool -> Bool -> Bool
False && x   = False
True  && x   = x
False || x   = x
True  || x   = True

not         :: Bool -> Bool
not True     = False
not False    = True

otherwise   :: Bool
otherwise    = True

--instance Eq Bool where    done in Prelude.java
  
--instance Ord Bool where 

--instance Ix Bool where 
--  range (False, False) = [False]
--  range (False, True)  = [False, True]
--  range (True, False)  = []
--  range (True, True)   = [True]
  
--  index (False, False) False = 0
--  index (False, False) True  = error ""
--  index (False, True)  False = 0
--  index (False, True)  True  = 1
--  index (True, False)  False = error ""
--  index (True, False)  True  = error ""
--  index (True, True)   False = error ""
--  index (True, True)   True  = 0

--  inRange (False, False) False = True
--  inRange (False, False) True  = False
--  inRange (False, True)  False = True
--  inRange (False, True)  True  = True
--  inRange (True, False)  False = False
--  inRange (True, False)  True  = False
--  inRange (True, True)   False = False
--  inRange (True, True)   True  = True


--instance Enum Bool where 

--instance Read Bool where 

--instance Show Bool where 

--instance Bounded Bool where 

-- Character type -----------------------------------------------------------

data Char = Char Nat    -- Aprove interprets it as natural number
type String = [Char]    -- strings are lists of characters

primEqChar    :: Char -> Char -> Bool
primEqChar (Char x) (Char y) = primEqNat x y

primCmpChar   :: Char -> Char -> Ordering
primCmpChar (Char x) (Char y) = primCmpNat x y

instance Eq Char  where (==)    = primEqChar
instance Ord Char where compare = primCmpChar

primCharToInt :: Char -> Int
primCharToInt (Char x) = Pos x

primIntToChar :: Int -> Char
primIntToChar (Pos x)    = Char x
primIntToChar (Neg Zero) = Char Zero

instance Enum Char where
    toEnum           = primIntToChar
    fromEnum         = primCharToInt
    enumFrom c       = map toEnum [fromEnum c .. fromEnum (maxBound::Char)]
    enumFromThen c d = map toEnum [fromEnum c, fromEnum d .. fromEnum (lastChar::Char)]
		       where lastChar = if d < c then minBound else maxBound

instance Ix Char where
    range (c,c')      = [c..c']
    index b@(c,c') ci
       | inRange b ci = fromEnum ci - fromEnum c
       | otherwise    = error "" -- "Ix.index: Index out of range."
    inRange (c,c') ci = fromEnum c <= i && i <= fromEnum c'
			where i = fromEnum ci

instance Read Char where
    readsPrec p      = readParen False
			    (\r -> [(c,t) | ('\'':s,t) <- lex r,
					    (c,"\'")   <- readLitChar s ])
    readList = readParen False (\r -> [(l,t) | ('"':s, t) <- lex r,
					       (l,_)      <- readl s ])
	       where readl ('"':s)      = [("",s)]
		     readl ('\\':'&':s) = readl s
		     readl s            = [(c:cs,u) | (c ,t) <- readLitChar s,
						      (cs,u) <- readl t ]
instance Show Char where
    showsPrec p '\'' = showString "'\\''"
    showsPrec p c    = showChar '\'' . showLitChar c . showChar '\''

    showList cs   = showChar '"' . showl cs
		    where showl ""       = showChar '"'
			  showl ('"':cs) = showString "\\\"" . showl cs
			  showl (c:cs)   = showLitChar c . showl cs

instance Bounded Char where
    minBound = '\0'
    maxBound = '\255'

isAscii, isLatin1, isControl, isPrint, isSpace  :: Char -> Bool
isUpper, isLower, isAlpha, isDigit, isAlphaNum  :: Char -> Bool
isAscii c              =  fromEnum c < 128
isLatin1 c             =  c <= '\xff'
isControl c            =  c < ' ' || c >= '\DEL' && c <= '\x9f'
isPrint c              =  not (isControl c)
isSpace c              =  c == ' '  ||
			  c == '\t' ||
			  c == '\n' ||
			  c == '\r' ||
			  c == '\f' ||
			  c == '\v' ||
			  c == '\xa0'

isUpper c              =  c >= 'A'    && c <= 'Z'    ||
                          c >= '\xc0' && c <= '\xd6' ||
                          c >= '\xd8' && c <= '\xde'

isLower c              =  c >= 'a'   &&  c <= 'z'    ||
                          c >= '\xdf' && c <= '\xf6' ||
                          c >= '\xf8' && c <= '\xff'

isAlpha c              =  isUpper c  ||  isLower c
isDigit c              =  c >= '0'   &&  c <= '9'
isAlphaNum c           =  isAlpha c  ||  isDigit c

-- Digit conversion operations
digitToInt :: Char -> Int
digitToInt c
  | isDigit c            =  fromEnum c - fromEnum '0'
  | c >= 'a' && c <= 'f' =  fromEnum c - fromEnum 'a' + 10
  | c >= 'A' && c <= 'F' =  fromEnum c - fromEnum 'A' + 10
  | otherwise            =  error "" --"Char.digitToInt: not a digit"

intToDigit :: Int -> Char
intToDigit i
  | i >= 0  && i <=  9   =  toEnum (fromEnum '0' + i)
  | i >= 10 && i <= 15   =  toEnum (fromEnum 'a' + i - 10)
  | otherwise            =  error "" --"Char.intToDigit: not a digit"

toUpper, toLower      :: Char -> Char
toUpper c | c == '\xdf' || c == '\xff' = c      -- lower, but no upper
	  | isLower c  = toEnum (fromEnum c - fromEnum 'a' + fromEnum 'A')
	  | otherwise  = c

toLower c | isUpper c  = toEnum (fromEnum c - fromEnum 'A' + fromEnum 'a')
	  | otherwise  = c

ord         	      :: Char -> Int
ord         	       = fromEnum

chr                   :: Int -> Char
chr                    = toEnum

-- Maybe type ---------------------------------------------------------------

data Maybe a = Nothing | Just a
       deriving (Eq, Ord, Read, Show)

maybe             :: b -> (a -> b) -> Maybe a -> b
maybe n f Nothing  = n
maybe n f (Just x) = f x

instance Functor Maybe where
    fmap f Nothing  = Nothing
    fmap f (Just x) = Just (f x)

instance Monad Maybe where
    Just x  >>= k = k x
    Nothing >>= k = Nothing
    return        = Just
    fail s        = Nothing

-- Either type --------------------------------------------------------------

data Either a b = Left a | Right b
		  deriving (Eq, Ord, Read, Show)

either              :: (a -> c) -> (b -> c) -> Either a b -> c
either l r (Left x)  = l x
either l r (Right y) = r y

-- Ordering type ------------------------------------------------------------

data Ordering = LT | EQ | GT
		deriving (Eq, Ord, Ix, Enum, Read, Show, Bounded)

-- Lists --------------------------------------------------------------------

-- data [a] = [] | a : [a] deriving (Eq, Ord)

instance Eq a => Eq [a] where
    []     == []     =  True
    (x:xs) == (y:ys) =  x==y && xs==ys
    _      == _      =  False

instance Ord a => Ord [a] where
    compare []     (_:_)  = LT
    compare []     []     = EQ
    compare (_:_)  []     = GT
    compare (x:xs) (y:ys) = primCompAux x y (compare xs ys)

instance Functor [] where
    fmap = map

instance Monad [ ] where
    (x:xs) >>= f = f x ++ (xs >>= f)
    []     >>= f = []
    return x     = [x]
    fail s       = []

instance Read a => Read [a]  where
    readsPrec p = readList

instance Show a => Show [a]  where
    showsPrec p = showList

-- Tuples -------------------------------------------------------------------

-- data (a,b) = (a,b) deriving (Eq, Ord, Ix, Read, Show)
-- etc..

-- Standard Integral types --------------------------------------------------

data Int = Pos Nat | Neg Nat  -- Aprove Standard implementation 
data Nat = Succ Nat | Zero
data Integer = Integer Int 



instance Eq  Int     where (==)                            = primEqInt
instance Eq  Integer where (==)    (Integer x) (Integer y) = primEqInt x y
instance Ord Int     where compare                         = primCmpInt
instance Ord Integer where compare (Integer x) (Integer y) = primCmpInt x y 

instance Num Int where
    (+)           = primPlusInt
    (-)           = primMinusInt
    negate        = primNegInt
    (*)           = primMulInt
    abs           = absReal
    signum        = signumReal
    fromInteger (Integer x) = x
    fromInt x     = x

primMinInt :: Int
primMinInt = primMinInt

primMaxInt :: Int
primMaxInt = primMaxInt

instance Bounded Int where
    minBound = primMinInt
    maxBound = primMaxInt
    
instance Num Integer where
    (+)     (Integer x) (Integer y)  = Integer (primPlusInt x y)
    (-)     (Integer x) (Integer y)  = Integer (primMinusInt x y)
    negate  (Integer x)              = Integer (primNegInt x)
    (*)     (Integer x) (Integer y)  = Integer (primMulInt x y)
    abs           = absReal
    signum        = signumReal
    fromInteger x = x
    fromInt     x = (Integer x)

absReal x    | x >= 0    =  x
             | otherwise = -x

signumReal x | x == 0    =  0
             | x > 0     =  1
             | otherwise = -1

instance Real Int where
    toRational x = toInteger x % 1

instance Real Integer where
    toRational x = x % 1

primPlusInt :: Int -> Int -> Int
primPlusInt (Pos x) (Neg y) = primMinusNat x y
primPlusInt (Neg x) (Pos y) = primMinusNat y x
primPlusInt (Neg x) (Neg y) = Neg (primPlusNat x y)
primPlusInt (Pos x) (Pos y) = Pos (primPlusNat x y)

primPlusNat  :: Nat -> Nat -> Nat
primPlusNat Zero    Zero      = Zero
primPlusNat Zero    (Succ y)  = Succ y
primPlusNat (Succ x) (Zero)   = Succ x
primPlusNat (Succ x) (Succ y) = Succ (Succ (primPlusNat x y))

primMinusInt :: Int -> Int -> Int
primMinusInt (Pos x) (Neg y) = Pos (primPlusNat x y)
primMinusInt (Neg x) (Pos y) = Neg (primPlusNat x y)
primMinusInt (Neg x) (Neg y) = primMinusNat y x
primMinusInt (Pos x) (Pos y) = primMinusNat x y

primMinusNat :: Nat -> Nat -> Int
primMinusNat Zero    Zero      = Pos Zero 
primMinusNat Zero    (Succ y)  = Neg (Succ y)
primMinusNat (Succ x) (Zero)   = Pos (Succ x)
primMinusNat (Succ x) (Succ y) = primMinusNat x y

primEvenInt :: Int -> Bool  
primEvenInt (Pos x)         = primEvenNat x
primEvenInt (Neg x)         = primEvenNat x

primEvenNat :: Nat -> Bool
primEvenNat Zero            = True
primEvenNat (Succ Zero)     = False
primEvenNat (Succ (Succ x)) = primEvenNat x

primMulInt :: Int -> Int -> Int
primMulInt (Pos x) (Pos y) = Pos (primMulNat x y)
primMulInt (Pos x) (Neg y) = Neg (primMulNat x y)
primMulInt (Neg x) (Pos y) = Neg (primMulNat x y)
primMulInt (Neg x) (Neg y) = Pos (primMulNat x y)

primMulNat :: Nat -> Nat -> Nat
primMulNat Zero    Zero      = Zero 
primMulNat Zero    (Succ y)  = Zero
primMulNat (Succ x) (Zero)   = Zero
primMulNat (Succ x) (Succ y) = primPlusNat (primMulNat x (Succ y)) (Succ y)

primNegInt :: Int -> Int
primNegInt (Pos x) = Neg x
primNegInt (Neg x) = Pos x

primCmpInt :: Int -> Int -> Ordering
primCmpInt (Pos Zero) (Pos Zero) = EQ
primCmpInt (Pos Zero) (Neg Zero) = EQ
primCmpInt (Neg Zero) (Pos Zero) = EQ
primCmpInt (Neg Zero) (Neg Zero) = EQ
primCmpInt (Pos x) (Pos y) = primCmpNat x y
primCmpInt (Pos x) (Neg y) = GT
primCmpInt (Neg x) (Pos y) = LT
primCmpInt (Neg x) (Neg y) = primCmpNat y x 

primCmpNat :: Nat -> Nat -> Ordering
primCmpNat Zero     Zero     = EQ
primCmpNat Zero     (Succ y) = LT
primCmpNat (Succ x) (Zero)   = GT
primCmpNat (Succ x) (Succ y) = primCmpNat x y


primEqInt :: Int -> Int -> Bool
primEqInt (Pos (Succ x)) (Pos (Succ y)) = primEqNat x y
primEqInt (Neg (Succ x)) (Neg (Succ y)) = primEqNat x y
primEqInt (Pos Zero) (Neg Zero) = True
primEqInt (Neg Zero) (Pos Zero) = True
primEqInt (Neg Zero) (Neg Zero) = True
primEqInt (Pos Zero) (Pos Zero) = True
primEqInt _ _                   = False

primEqNat      :: Nat -> Nat -> Bool
primEqNat Zero     Zero     = True
primEqNat Zero     (Succ y) = False
primEqNat (Succ x) (Zero)   = False
primEqNat (Succ x) (Succ y) = primEqNat x y


primDivNatS :: Nat -> Nat -> Nat
primDivNatS Zero     Zero      = error ""
primDivNatS (Succ x) Zero      = error ""
primDivNatS (Succ x) (Succ y)  = if (primGEqNatS x y) then Succ (primDivNatS (primMinusNatS x y) (Succ y)) else Zero
primDivNatS Zero     (Succ x)  = Zero

primDivNatP :: Nat -> Nat -> Nat
primDivNatP Zero     Zero      = error ""
primDivNatP (Succ x) Zero      = error ""
primDivNatP (Succ x) (Succ y)  = Succ (primDivNatP (primMinusNatS x y) (Succ y))
primDivNatP Zero     (Succ x)  = Zero

primMinusNatS :: Nat -> Nat -> Nat
primMinusNatS (Succ x) (Succ y) = primMinusNatS x y
primMinusNatS Zero     (Succ y) = Zero
primMinusNatS x        Zero     = x

primGEqNatS :: Nat -> Nat -> Bool
primGEqNatS (Succ x) Zero = True
primGEqNatS (Succ x) (Succ y) = (primGEqNatS x y)
primGEqNatS Zero (Succ x) = False
primGEqNatS Zero Zero = True

primModNatS :: Nat -> Nat -> Nat
primModNatS Zero     Zero      = error ""
primModNatS (Succ x) Zero      = error ""
primModNatS (Succ x) (Succ y)  = if (primGEqNatS x y) then (primModNatS (primMinusNatS x y) (Succ y)) else (Succ x)
primModNatS Zero     (Succ x)  = Zero

primModNatP :: Nat -> Nat -> Nat
primModNatP Zero     Zero      = error ""
primModNatP (Succ x) Zero      = error ""
primModNatP (Succ x) (Succ y)  = if (primGEqNatS x y) then (primModNatP (primMinusNatS x y) (Succ y)) else (primMinusNatS y x)
primModNatP Zero     (Succ x)  = Zero


primQuotInt :: Int -> Int -> Int
primQuotInt (Pos x) (Pos (Succ y)) = Pos (primDivNatS x (Succ y))
primQuotInt (Pos x) (Neg (Succ y)) = Neg (primDivNatS x (Succ y))
primQuotInt (Neg x) (Pos (Succ y)) = Neg (primDivNatS x (Succ y))
primQuotInt (Neg x) (Neg (Succ y)) = Pos (primDivNatS x (Succ y))
primQuotInt _ _     = error ""

primDivInt :: Int -> Int -> Int
primDivInt (Pos x) (Pos (Succ y)) = Pos (primDivNatS x (Succ y))
primDivInt (Pos x) (Neg (Succ y)) = Neg (primDivNatP x (Succ y))
primDivInt (Neg x) (Pos (Succ y)) = Neg (primDivNatP x (Succ y))
primDivInt (Neg x) (Neg (Succ y)) = Pos (primDivNatS x (Succ y))
primDivInt _ _     = error ""


primRemInt  :: Int -> Int -> Int
primRemInt (Pos x) (Pos (Succ y)) = Pos (primModNatS x (Succ y))
primRemInt (Pos x) (Neg (Succ y)) = Pos (primModNatS x (Succ y))
primRemInt (Neg x) (Pos (Succ y)) = Neg (primModNatS x (Succ y))
primRemInt (Neg x) (Neg (Succ y)) = Neg (primModNatS x (Succ y))
primRemInt _ _ = error ""

primModInt  :: Int -> Int -> Int
primModInt (Pos x) (Pos (Succ y)) = Pos (primModNatS x (Succ y))
primModInt (Pos x) (Neg (Succ y)) = Neg (primModNatP x (Succ y))
primModInt (Neg x) (Pos (Succ y)) = Pos (primModNatP x (Succ y))
primModInt (Neg x) (Neg (Succ y)) = Neg (primModNatS x (Succ y))
primModInt _ _ = error ""

primQrmInt :: Int -> Int -> (Int, Int)
primQrmInt x y = (primQuotInt x y, primRemInt x y)

instance Integral Int where
    div         = primDivInt
    quot        = primQuotInt
    rem         = primRemInt
    mod         = primModInt
    quotRem     = primQrmInt
    even        = primEvenInt
    toInteger x = (Integer x)
    toInt x   = x

instance Integral Integer where
    div  (Integer x) (Integer y) = Integer (primDivInt x y)
    quot (Integer x) (Integer y) = Integer (primQuotInt x y)
    rem  (Integer x) (Integer y) = Integer (primRemInt x y)
    mod  (Integer x) (Integer y) = Integer (primModInt x y)
    quotRem (Integer x) (Integer y) = (Integer (primQuotInt x y), Integer (primRemInt x y))
    even (Integer x)             = primEvenInt x
    toInteger x                  = x
    toInt (Integer x)            = x

instance Ix Int where
    range (m,n)          = [m..n]
    index b@(m,n) i
	   | inRange b i = i - m
	   | otherwise   = error "" --"index: Index out of range"
    inRange (m,n) i      = m <= i && i <= n

instance Ix Integer where
    range (m,n)          = [m..n]
    index b@(m,n) i
	   | inRange b i = fromInteger (i - m)
	   | otherwise   = error "" --"index: Index out of range"
    inRange (m,n) i      = m <= i && i <= n

instance Enum Int where
    succ (Pos Zero) = Pos (Succ Zero)
    succ (Neg Zero) = Pos (Succ Zero)
    succ (Pos (Succ x)) = Pos (Succ (Succ x))
    succ (Neg (Succ x)) = Neg x
    pred (Pos Zero) = Neg (Succ Zero)
    pred (Neg Zero) = Neg (Succ Zero)
    pred (Pos (Succ x)) = Pos x
    pred (Neg (Succ x)) = Neg (Succ (Succ x))
    
    toEnum               = id
    fromEnum             = id
    enumFrom       = numericEnumFrom
    enumFromTo     = numericEnumFromTo
    enumFromThen   = numericEnumFromThen
    enumFromThenTo = numericEnumFromThenTo

instance Enum Integer where
    succ     (Integer x) = Integer (succ x)
    pred     (Integer x) = Integer (pred x)

    toEnum   x           = Integer x
    fromEnum (Integer x) = x
    enumFrom             = numericEnumFrom
    enumFromThen         = numericEnumFromThen
    enumFromTo           = numericEnumFromTo
    enumFromThenTo       = numericEnumFromThenTo


numericEnumFrom        :: Real a => a -> [a]
numericEnumFromThen    :: Real a => a -> a -> [a]
numericEnumFromTo      :: Real a => a -> a -> [a]
numericEnumFromThenTo  :: Real a => a -> a -> a -> [a]
numericEnumFrom n            = n : (numericEnumFrom $! (n+1))
numericEnumFromThen n m      = iterate ((m-n)+) n
numericEnumFromTo n m        = takeWhile (<= m) (numericEnumFrom n)
numericEnumFromThenTo n n' m = takeWhile p (numericEnumFromThen n n')
                               where p | n' >= n   = (<= m)
				       | otherwise = (>= m)

primShowInt :: Int -> [Char]                       
primShowInt (Pos Zero)     = "0"
primShowInt (Pos (Succ x)) = primShowInt (div (Pos (Succ x)) 10) ++ [ toEnum (mod (Pos (Succ x)) 10) ]
primShowInt (Neg x) = '-' : primShowInt (Pos x)


--primShowsInt :: Int -> Int -> ShowS
--primShowsInt = primShowsInt

instance Read Int where
    readsPrec p = readSigned readDec

instance Show Int where
    show = primShowInt

instance Read Integer where
    readsPrec p = readSigned readDec

instance Show Integer where
    show (Integer x)  = primShowInt x

-- Standard Floating types --------------------------------------------------

data Float = Float Int Int    -- builtin datatype of single precision floating point numbers
data Double = Double Int Int  -- builtin datatype of double precision floating point numbers

primEqFloat   :: Float -> Float -> Bool
primEqFloat (Float x1 x2) (Float y1 y2) = (x1*y2) == (x2*y1)

primCmpFloat  :: Float -> Float -> Ordering
primCmpFloat (Float x1 (Pos x2)) (Float y1 (Pos y2)) = compare (x1*(Pos y2)) ((Pos x2)*y1)
primCmpFloat (Float x1 (Pos x2)) (Float y1 (Neg y2)) = compare (x1*(Pos y2)) ((Neg x2)*y1)
primCmpFloat (Float x1 (Neg x2)) (Float y1 (Pos y2)) = compare (x1*(Neg y2)) ((Pos x2)*y1)
primCmpFloat (Float x1 (Neg x2)) (Float y1 (Neg y2)) = compare (x1*(Neg y2)) ((Neg x2)*y1)

primEqDouble  :: Double -> Double -> Bool
primEqDouble (Double x1 x2) (Double y1 y2) = (x1*y2) == (x2*y1)

primCmpDouble :: Double -> Double -> Ordering
primCmpDouble (Double x1 (Pos x2)) (Double y1 (Pos y2)) = compare (x1*(Pos y2)) ((Pos x2)*y1)
primCmpDouble (Double x1 (Pos x2)) (Double y1 (Neg y2)) = compare (x1*(Pos y2)) ((Neg x2)*y1)
primCmpDouble (Double x1 (Neg x2)) (Double y1 (Pos y2)) = compare (x1*(Neg y2)) ((Pos x2)*y1)
primCmpDouble (Double x1 (Neg x2)) (Double y1 (Neg y2)) = compare (x1*(Neg y2)) ((Neg x2)*y1)

instance Eq  Float  where (==) = primEqFloat
instance Eq  Double where (==) = primEqDouble

instance Ord Float  where compare = primCmpFloat
instance Ord Double where compare = primCmpDouble

primPlusFloat      :: Float -> Float -> Float 
primPlusFloat  (Float x1 x2) (Float y1 y2) = Float (x1*y2+y1*x2) (x2*y2)

primMinusFloat     :: Float -> Float -> Float  
primMinusFloat (Float x1 x2) (Float y1 y2) = Float (x1*y2-y1*x2) (x2*y2)

primMulFloat       :: Float -> Float -> Float
primMulFloat   (Float x1 x2) (Float y1 y2) = Float (x1*y1) (x2*y2)

primNegFloat       :: Float -> Float
primNegFloat   (Float x1 x2) = Float (-x1) x2

primIntToFloat     :: Int -> Float
primIntToFloat x = Float x 1

primIntegerToFloat :: Integer -> Float
primIntegerToFloat (Integer x) = primIntToFloat x

instance Num Float where
    (+)           = primPlusFloat
    (-)           = primMinusFloat
    negate        = primNegFloat
    (*)           = primMulFloat
    abs           = absReal
    signum        = signumReal
    fromInteger   = primIntegerToFloat
    fromInt       = primIntToFloat

primPlusDouble      :: Double -> Double -> Double
primPlusDouble  (Double x1 x2) (Double y1 y2) = Double (x1*y2+y1*x2) (x2*y2)

primMinusDouble     :: Double -> Double -> Double 
primMinusDouble (Double x1 x2) (Double y1 y2) = Double (x1*y2-y1*x2) (x2*y2)

primMulDouble       :: Double -> Double -> Double
primMulDouble   (Double x1 x2) (Double y1 y2) = Double (x1*y1) (x2*y2)

primNegDouble       :: Double -> Double
primNegDouble   (Double x1 x2) = Double (-x1) x2

primIntToDouble     :: Int -> Double
primIntToDouble x = Double x 1

primIntegerToDouble :: Integer -> Double
primIntegerToDouble (Integer x) = primIntToDouble x

instance Num Double where
    (+)         = primPlusDouble
    (-)         = primMinusDouble
    negate      = primNegDouble
    (*)         = primMulDouble
    abs         = absReal
    signum      = signumReal
    fromInteger = primIntegerToDouble
    fromInt     = primIntToDouble

instance Real Float where
    toRational = floatToRational

instance Real Double where
    toRational = doubleToRational

-- Calls to these functions are optimised when passed as arguments to
-- fromRational.
floatToRational  :: Float  -> Rational
floatToRational (Float x y) = (Integer x)%(Integer y)

doubleToRational :: Double -> Rational
doubleToRational (Double x y) = (Integer x)%(Integer y)

{-
realFloatToRational x = (m%1)*(b%1)^^n
			where (m,n) = decodeFloat x
			      b     = floatRadix x
-}

primDivFloat      :: Float -> Float -> Float
primDivFloat   (Float x1 x2) (Float y1 y2) = Float (x1*y2) (x2*y1)

doubleToFloat     :: Double -> Float
doubleToFloat (Double x y) = Float x y

instance Fractional Float where
    (/)          = primDivFloat
    fromRational = primRationalToFloat
    fromDouble   = doubleToFloat

primDivDouble :: Double -> Double -> Double
primDivDouble   (Double x1 x2) (Double y1 y2) = Double (x1*y2) (x2*y1)

instance Fractional Double where
    (/)          = primDivDouble
    fromRational = primRationalToDouble
    fromDouble x = x

-- These primitives are equivalent to (and are defined using)
-- rationalTo{Float,Double}.  The difference is that they test to see
-- if their argument is of the form (fromDouble x) - which allows a much
-- more efficient implementation.
primRationalToFloat  :: Rational -> Float
primRationalToFloat = rationalToFloat

primRationalToDouble :: Rational -> Double
primRationalToDouble = rationalToDouble

-- These functions are used by Hugs - don't change their types.
rationalToFloat  :: Rational -> Float
rationalToFloat ( (Integer x) :% (Integer y) ) = Float x y

rationalToDouble :: Rational -> Double
rationalToDouble ( (Integer x) :% (Integer y) ) = Double x y

{-
rationalToFloat = rationalToRealFloat
rationalToDouble = rationalToRealFloat

rationalToRealFloat x = x'
 where x'    = f e
       f e   = if e' == e then y else f e'
	       where y      = encodeFloat (round (x * (1%b)^^e)) e
		     (_,e') = decodeFloat y
       (_,e) = decodeFloat (fromInteger (numerator x) `asTypeOf` x'
			     / fromInteger (denominator x))
       b     = floatRadix x'
-}

primSinFloat  :: Float -> Float
primSinFloat = terminator

primAsinFloat :: Float -> Float
primAsinFloat = terminator

primCosFloat  :: Float -> Float
primCosFloat = terminator

primAcosFloat :: Float -> Float 
primAcosFloat = terminator

primTanFloat  :: Float -> Float
primTanFloat = terminator

primAtanFloat :: Float -> Float
primAtanFloat = terminator

primLogFloat  :: Float -> Float
primLogFloat = terminator

primExpFloat  :: Float -> Float
primExpFloat = terminator

primSqrtFloat :: Float -> Float
primSqrtFloat = terminator

instance Floating Float where
    exp   = primExpFloat
    log   = primLogFloat
    sqrt  = primSqrtFloat
    sin   = primSinFloat
    cos   = primCosFloat
    tan   = primTanFloat
    asin  = primAsinFloat
    acos  = primAcosFloat
    atan  = primAtanFloat

primSinDouble  :: Double -> Double
primSinDouble = terminator

primAsinDouble :: Double -> Double
primAsinDouble = terminator

primCosDouble  :: Double -> Double
primCosDouble = terminator

primAcosDouble :: Double -> Double 
primAcosDouble = terminator

primTanDouble  :: Double -> Double
primTanDouble = terminator

primAtanDouble :: Double -> Double
primAtanDouble = terminator

primLogDouble  :: Double -> Double
primLogDouble = terminator

primExpDouble  :: Double -> Double
primExpDouble = terminator

primSqrtDouble :: Double -> Double
primSqrtDouble = terminator

instance Floating Double where
    exp   = primExpDouble
    log   = primLogDouble
    sqrt  = primSqrtDouble
    sin   = primSinDouble
    cos   = primCosDouble
    tan   = primTanDouble
    asin  = primAsinDouble
    acos  = primAcosDouble
    atan  = primAtanDouble

instance RealFrac Float where
    properFraction = floatProperFractionFloat

instance RealFrac Double where
    properFraction = floatProperFractionDouble

{-
floatProperFraction x
   | n >= 0      = (fromInteger m * fromInteger b ^ n, 0)
   | otherwise   = (fromInteger w, encodeFloat r n)
		   where (m,n) = decodeFloat x
			 b     = floatRadix x
			 (w,r) = quotRem m (b^(-n))
-}
floatProperFractionFloat  frac@(Float  x y) = ( fromInt (x `quot` y), frac-(fromInt (x `quot` y)) )
floatProperFractionDouble frac@(Double x y) = ( fromInt (x `quot` y), frac-(fromInt (x `quot` y)) )


primFloatRadix  :: Integer
primFloatRadix = 2

primFloatDigits :: Int
primFloatDigits = 24

primFloatMinExp :: Int 
primFloatMinExp = -125

primFloatMaxExp :: Int
primFloatMaxExp = 128

primFloatEncode :: Integer -> Int -> Float
--primFloatEncode = primFloatEncode
primFloatEncode x y = (fromInteger x) * (power 2 y)
		where	power :: Int -> Int -> Float
			power _ 0 = 1.0
			power x (y+1) = (fromInt x)*(power x y)
			power x y = 1.0/(power x (-y))

primFloatDecode :: Float -> (Integer, Int)
primFloatDecode = terminator


instance RealFloat Float where
    floatRadix  _ = primFloatRadix
    floatDigits _ = primFloatDigits
    floatRange  _ = (primFloatMinExp, primFloatMaxExp)
    encodeFloat = primFloatEncode
    decodeFloat = primFloatDecode                   
    isNaN       _ = False
    isInfinite  _ = False
    isDenormalized _ = False
    isNegativeZero _ = False
    isIEEE      _ = False

primDoubleRadix  :: Integer
primDoubleRadix = 2

primDoubleDigits :: Int
primDoubleDigits = 53

primDoubleMinExp :: Int 
primDoubleMinExp = -1021

primDoubleMaxExp :: Int
primDoubleMaxExp = 1024

primDoubleEncode :: Integer -> Int -> Double
primDoubleEncode x y = (fromInteger x) * (power 2 y)
		where	power :: Int -> Int -> Double
			power _ 0 = 1.0
			power x (y+1) = (fromInt x)*(power x y)
			power x y = 1.0/(power x (-y))

primDoubleDecode :: Double -> (Integer, Int)
primDoubleDecode = terminator

instance RealFloat Double where
    floatRadix  _ = primDoubleRadix
    floatDigits _ = primDoubleDigits
    floatRange  _ = (primDoubleMinExp, primDoubleMaxExp)
    encodeFloat   = primDoubleEncode
    decodeFloat   = primDoubleDecode
    isNaN       _ = False
    isInfinite  _ = False
    isDenormalized _ = False
    isNegativeZero _ = False
    isIEEE      _ = False

instance Enum Float where
    toEnum		  = primIntToFloat
    fromEnum		  = truncate
    enumFrom		  = numericEnumFrom
    enumFromThen	  = numericEnumFromThen
    enumFromTo n m	  = numericEnumFromTo n (m+1/2)
    enumFromThenTo n n' m = numericEnumFromThenTo n n' (m + (n'-n)/2)

instance Enum Double where
    toEnum		  = primIntToDouble
    fromEnum		  = truncate
    enumFrom		  = numericEnumFrom
    enumFromThen	  = numericEnumFromThen
    enumFromTo n m	  = numericEnumFromTo n (m+1/2)
    enumFromThenTo n n' m = numericEnumFromThenTo n n' (m + (n'-n)/2)

primShowsFloat :: Int -> Float -> ShowS
primShowsFloat = terminator

instance Read Float where
    readsPrec p = readSigned readFloat

-- Note that showFloat in Numeric isn't used here
instance Show Float where
    showsPrec   = primShowsFloat

primShowsDouble :: Int -> Double -> ShowS
primShowsDouble = terminator

instance Read Double where
    readsPrec p = readSigned readFloat

-- Note that showFloat in Numeric isn't used here
instance Show Double where
    showsPrec   = primShowsDouble

-- Some standard functions --------------------------------------------------

fst            :: (a,b) -> a
fst (x,_)       = x

snd            :: (a,b) -> b
snd (_,y)       = y

curry          :: ((a,b) -> c) -> (a -> b -> c)
curry f x y     = f (x,y)

uncurry        :: (a -> b -> c) -> ((a,b) -> c)
uncurry f p     = f (fst p) (snd p)

id             :: a -> a
id    x         = x

const          :: a -> b -> a
const k _       = k

(.)            :: (b -> c) -> (a -> b) -> (a -> c)
(f . g) x       = f (g x)

flip           :: (a -> b -> c) -> b -> a -> c
flip f x y      = f y x

($)            :: (a -> b) -> a -> b
f $ x           = f x

until          :: (a -> Bool) -> (a -> a) -> a -> a
until p f x     = if p x then x else until p f (f x)

asTypeOf       :: a -> a -> a
asTypeOf        = const

error  :: String -> b
error _ = undefined

undefined        :: a
undefined | False = undefined

-- Standard functions on rational numbers {PreludeRatio} --------------------

data Integral a => Ratio a = !a :% !a deriving (Eq)
type Rational              = Ratio Integer

(%)                       :: Integral a => a -> a -> Ratio a
x % y                      = reduce (x * signum y) (abs y)

reduce                    :: Integral a => a -> a -> Ratio a
reduce x y | y == 0        = error "" --"Ratio.%: zero denominator"
	   | otherwise     = (x `quot` d) :% (y `quot` d)
			     where d = gcd x y

numerator, denominator    :: Integral a => Ratio a -> a
numerator (x :% y)         = x
denominator (x :% y)       = y

instance Integral a => Ord (Ratio a) where
    compare (x:%y) (x':%y') = compare (x*y') (x'*y)

instance Integral a => Num (Ratio a) where
    (x:%y) + (x':%y') = reduce (x*y' + x'*y) (y*y')
    (x:%y) * (x':%y') = reduce (x*x') (y*y')
    negate (x :% y)   = negate x :% y
    abs (x :% y)      = abs x :% y
    signum (x :% y)   = signum x :% 1
    fromInteger x     = fromInteger x :% 1
    fromInt           = intToRatio

-- Hugs optimises code of the form fromRational (intToRatio x)
intToRatio :: Integral a => Int -> Ratio a
intToRatio x = fromInt x :% 1

instance Integral a => Real (Ratio a) where
    toRational (x:%y) = toInteger x :% toInteger y

instance Integral a => Fractional (Ratio a) where
    (x:%y) / (x':%y')   = (x*y') % (y*x')
    recip (x:%y)        = y :% x
    fromRational (x:%y) = fromInteger x :% fromInteger y
    fromDouble 		= doubleToRatio

-- Hugs optimises code of the form fromRational (doubleToRatio x)
doubleToRatio :: Integral a => Double -> Ratio a
{-
doubleToRatio x
	    | n>=0      = (fromInteger m * fromInteger b ^ n) % 1
	    | otherwise = fromInteger m % (fromInteger b ^ (-n))
			  where (m,n) = decodeFloat x
				b     = floatRadix x
-}
doubleToRatio (Double x y) = (fromInt x) % (fromInt y)


instance Integral a => RealFrac (Ratio a) where
    properFraction (x:%y) = (fromIntegral q, r:%y)
			    where (q,r) = quotRem x y

instance Integral a => Enum (Ratio a) where
    toEnum       = fromInt
    fromEnum     = truncate
    enumFrom     = numericEnumFrom
    enumFromThen = numericEnumFromThen

instance (Read a, Integral a) => Read (Ratio a) where
    readsPrec p = readParen (p > 7)
			    (\r -> [(x%y,u) | (x,s)   <- reads r,
					      ("%",t) <- lex s,
					      (y,u)   <- reads t ])

instance Integral a => Show (Ratio a) where
    showsPrec p (x:%y) = showParen (p > 7)
			     (shows x . showString " % " . shows y)

approxRational      :: RealFrac a => a -> a -> Rational
approxRational x eps = simplest (x-eps) (x+eps)
 where simplest x y | y < x     = simplest y x
		    | x == y    = xr
		    | x > 0     = simplest' n d n' d'
		    | y < 0     = - simplest' (-n') d' (-n) d
		    | otherwise = 0 :% 1
				  where xr@(n:%d) = toRational x
					(n':%d')  = toRational y
       simplest' n d n' d'        -- assumes 0 < n%d < n'%d'
		    | r == 0    = q :% 1
		    | q /= q'   = (q+1) :% 1
		    | otherwise = (q*n''+d'') :% n''
				  where (q,r)      = quotRem n d
					(q',r')    = quotRem n' d'
					(n'':%d'') = simplest' d' r' d r

-- Standard list functions {PreludeList} ------------------------------------

head             :: [a] -> a
head (x:_)        = x

last             :: [a] -> a
last [x]          = x
last (_:xs)       = last xs

tail             :: [a] -> [a]
tail (_:xs)       = xs

init             :: [a] -> [a]
init [x]          = []
init (x:xs)       = x : init xs

null             :: [a] -> Bool
null []           = True
null (_:_)        = False

(++)             :: [a] -> [a] -> [a]
[]     ++ ys      = ys
(x:xs) ++ ys      = x : (xs ++ ys)

map              :: (a -> b) -> [a] -> [b]
map f []          = []
map f (x:xs)      = f x : (map f xs)

filter           :: (a -> Bool) -> [a] -> [a]
filter p xs       = [ x | x <- xs, p x ]

concat           :: [[a]] -> [a]
concat            = foldr (++) []

length           :: [a] -> Int
length            = foldl' (\n _ -> n + 1) 0

(!!)             :: [a] -> Int -> a
(x:_)  !! 0       = x
(_:xs) !! n | n>0 = xs !! (n-1)
(_:_)  !! _       = error "" --"Prelude.!!: negative index"
[]     !! _       = error "" --"Prelude.!!: index too large"

foldl            :: (a -> b -> a) -> a -> [b] -> a
foldl f z []      = z
foldl f z (x:xs)  = foldl f (f z x) xs

foldl'           :: (a -> b -> a) -> a -> [b] -> a
foldl' f a []     = a
foldl' f a (x:xs) = (foldl' f $! f a x) xs

foldl1           :: (a -> a -> a) -> [a] -> a
foldl1 f (x:xs)   = foldl f x xs

scanl            :: (a -> b -> a) -> a -> [b] -> [a]
scanl f q xs      = q : (case xs of
			 []   -> []
			 x:xs -> scanl f (f q x) xs)

scanl1           :: (a -> a -> a) -> [a] -> [a]
scanl1 _ []       = []
scanl1 f (x:xs)   = scanl f x xs

foldr            :: (a -> b -> b) -> b -> [a] -> b
foldr f z []      = z
foldr f z (x:xs)  = f x (foldr f z xs)

foldr1           :: (a -> a -> a) -> [a] -> a
foldr1 f [x]      = x
foldr1 f (x:xs)   = f x (foldr1 f xs)

scanr            :: (a -> b -> b) -> b -> [a] -> [b]
scanr f q0 []     = [q0]
scanr f q0 (x:xs) = f x q : qs
		    where qs@(q:_) = scanr f q0 xs

scanr1           :: (a -> a -> a) -> [a] -> [a]
scanr1 f []       = []
scanr1 f [x]      = [x]
scanr1 f (x:xs)   = f x q : qs
		    where qs@(q:_) = scanr1 f xs

iterate          :: (a -> a) -> a -> [a]
iterate f x       = x : iterate f (f x)

repeat           :: a -> [a]
repeat x          = xs where xs = x:xs

replicate        :: Int -> a -> [a]
replicate n x     = take n (repeat x)

cycle            :: [a] -> [a]
cycle []          = error "" --"Prelude.cycle: empty list"
cycle xs          = xs' where xs'=xs++xs'

take                :: Int -> [a] -> [a]
take n _  | n <= 0  = []
take _ []           = []
take n (x:xs)       = x : take (n-1) xs

drop                :: Int -> [a] -> [a]
drop n xs | n <= 0  = xs
drop _ []           = []
drop n (_:xs)       = drop (n-1) xs

splitAt               :: Int -> [a] -> ([a], [a])
splitAt n xs | n <= 0 = ([],xs)
splitAt _ []          = ([],[])
splitAt n (x:xs)      = (x:xs',xs'') where (xs',xs'') = splitAt (n-1) xs

takeWhile           :: (a -> Bool) -> [a] -> [a]
takeWhile p []       = []
takeWhile p (x:xs)
	 | p x       = x : takeWhile p xs
	 | otherwise = []

dropWhile           :: (a -> Bool) -> [a] -> [a]
dropWhile p []       = []
dropWhile p xs@(x:xs')
	 | p x       = dropWhile p xs'
	 | otherwise = xs

span, break         :: (a -> Bool) -> [a] -> ([a],[a])
span p []            = ([],[])
span p xs@(x:xs')
	 | p x       = (x:ys, zs)
	 | otherwise = ([],xs)
                       where (ys,zs) = span p xs'
break p              = span (not . p)

lines     :: String -> [String]
lines ""   = []
lines s    = let (l,s') = break ('\n'==) s
             in l : case s' of []      -> []
                               (_:s'') -> lines s''

words     :: String -> [String]
words s    = case dropWhile isSpace s of
		  "" -> []
		  s' -> w : words s''
			where (w,s'') = break isSpace s'

unlines   :: [String] -> String
unlines []      = []
unlines (l:ls)  = l ++ '\n' : unlines ls

unwords   :: [String] -> String
unwords []	=  ""
unwords [w]	= w
unwords (w:ws)	= w ++ ' ' : unwords ws

reverse   :: [a] -> [a]
reverse    = foldl (flip (:)) []

and, or   :: [Bool] -> Bool
and        = foldr (&&) True
or         = foldr (||) False

any, all  :: (a -> Bool) -> [a] -> Bool
any p      = or  . map p
all p      = and . map p

elem, notElem    :: Eq a => a -> [a] -> Bool
elem              = any . (==)
notElem           = all . (/=)

lookup           :: Eq a => a -> [(a,b)] -> Maybe b
lookup k []       = Nothing
lookup k ((x,y):xys)
      | k==x      = Just y
      | otherwise = lookup k xys

sum, product     :: Num a => [a] -> a
sum               = foldl' (+) 0
product           = foldl' (*) 1

maximum, minimum :: Ord a => [a] -> a
maximum           = foldl1 max
minimum           = foldl1 min

concatMap        :: (a -> [b]) -> [a] -> [b]
concatMap f       = concat . map f

zip              :: [a] -> [b] -> [(a,b)]
zip               = zipWith  (\a b -> (a,b))

zip3             :: [a] -> [b] -> [c] -> [(a,b,c)]
zip3              = zipWith3 (\a b c -> (a,b,c))

zipWith                  :: (a->b->c) -> [a]->[b]->[c]
zipWith z (a:as) (b:bs)   = z a b : zipWith z as bs
zipWith _ _      _        = []

zipWith3                 :: (a->b->c->d) -> [a]->[b]->[c]->[d]
zipWith3 z (a:as) (b:bs) (c:cs)
			  = z a b c : zipWith3 z as bs cs
zipWith3 _ _ _ _          = []

unzip                    :: [(a,b)] -> ([a],[b])
unzip                     = foldr (\(a,b) ~(as,bs) -> (a:as, b:bs)) ([], [])

unzip3                   :: [(a,b,c)] -> ([a],[b],[c])
unzip3                    = foldr (\(a,b,c) ~(as,bs,cs) -> (a:as,b:bs,c:cs))
				  ([],[],[])

-- PreludeText ----------------------------------------------------------------

reads        :: Read a => ReadS a
reads         = readsPrec 0

shows        :: Show a => a -> ShowS
shows         = showsPrec 0

read         :: Read a => String -> a
read s        =  case [x | (x,t) <- reads s, ("","") <- lex t] of
		      [x] -> x
		      []  -> error "" --"Prelude.read: no parse"
		      _   -> error "" --"Prelude.read: ambiguous parse"

showChar     :: Char -> ShowS
showChar      = (:)

showString   :: String -> ShowS
showString    = (++)

showParen    :: Bool -> ShowS -> ShowS
showParen b p = if b then showChar '(' . p . showChar ')' else p

showField    :: Show a => String -> a -> ShowS
showField m v = showString m . showChar '=' . shows v

readParen    :: Bool -> ReadS a -> ReadS a
readParen b g = if b then mandatory else optional
		where optional r  = g r ++ mandatory r
		      mandatory r = [(x,u) | ("(",s) <- lex r,
					     (x,t)   <- optional s,
					     (")",u) <- lex t    ]

readField    :: Read a => String -> ReadS a
readField m s0 = [ r | (t,  s1) <- lex s0, t == m,
                       ("=",s2) <- lex s1,
                       r        <- reads s2 ]

lex                    :: ReadS String
lex ""                  = [("","")]
lex (c:s) | isSpace c   = lex (dropWhile isSpace s)
lex ('\'':s)            = [('\'':ch++"'", t) | (ch,'\'':t)  <- lexLitChar s,
					       ch /= "'"                ]
lex ('"':s)             = [('"':str, t)      | (str,t) <- lexString s]
			  where
			  lexString ('"':s) = [("\"",s)]
			  lexString s = [(ch++str, u)
						| (ch,t)  <- lexStrItem s,
						  (str,u) <- lexString t  ]

			  lexStrItem ('\\':'&':s) = [("\\&",s)]
			  lexStrItem ('\\':c:s) | isSpace c
			      = [("",t) | '\\':t <- [dropWhile isSpace s]]
			  lexStrItem s            = lexLitChar s

lex (c:s) | isSingle c  = [([c],s)]
	  | isSym c     = [(c:sym,t)         | (sym,t) <- [span isSym s]]
	  | isAlpha c   = [(c:nam,t)         | (nam,t) <- [span isIdChar s]]
	  | isDigit c   = [(c:ds++fe,t)      | (ds,s)  <- [span isDigit s],
					       (fe,t)  <- lexFracExp s     ]
	  | otherwise   = []    -- bad character
		where
		isSingle c  =  c `elem` ",;()[]{}_`"
		isSym c     =  c `elem` "!@#$%&*+./<=>?\\^|:-~"
		isIdChar c  =  isAlphaNum c || c `elem` "_'"

		lexFracExp ('.':c:cs) | isDigit c
                            = [('.':ds++e,u) | (ds,t) <- lexDigits (c:cs),
					       (e,u)  <- lexExp t    ]
		lexFracExp s       = lexExp s

		lexExp (e:s) | e `elem` "eE"
			 = [(e:c:ds,u) | (c:t)  <- [s], c `elem` "+-",
						   (ds,u) <- lexDigits t] ++
			   [(e:ds,t)   | (ds,t) <- lexDigits s]
		lexExp s = [("",s)]

lexDigits               :: ReadS String
lexDigits               =  nonnull isDigit

nonnull                 :: (Char -> Bool) -> ReadS String
nonnull p s             =  [(cs,t) | (cs@(_:_),t) <- [span p s]]

lexLitChar          :: ReadS String
lexLitChar ""       =  []
lexLitChar (c:s)
 | c /= '\\'        =  [([c],s)]
 | otherwise        =  map (prefix '\\') (lexEsc s)
 where
   lexEsc (c:s)     | c `elem` "abfnrtv\\\"'" = [([c],s)]
   lexEsc ('^':c:s) | c >= '@' && c <= '_'    = [(['^',c],s)]
    -- Numeric escapes
   lexEsc ('o':s)  = [prefix 'o' (span isOctDigit s)]
   lexEsc ('x':s)  = [prefix 'x' (span isHexDigit s)]
   lexEsc s@(c:_) 
     | isDigit c   = [span isDigit s]  
     | isUpper c   = case [(mne,s') | (c, mne) <- table,
	 	        ([],s') <- [lexmatch mne s]] of
                       (pr:_) -> [pr]
	               []     -> []
   lexEsc _        = []

   table = ('\DEL',"DEL") : asciiTab
   prefix c (t,s) = (c:t, s)

isOctDigit c  =  c >= '0' && c <= '7'
isHexDigit c  =  isDigit c || c >= 'A' && c <= 'F'
			   || c >= 'a' && c <= 'f'

lexmatch                   :: (Eq a) => [a] -> [a] -> ([a],[a])
lexmatch (x:xs) (y:ys) | x == y  =  lexmatch xs ys
lexmatch xs     ys               =  (xs,ys)

asciiTab = zip ['\NUL'..' ']
	   ["NUL", "SOH", "STX", "ETX", "EOT", "ENQ", "ACK", "BEL",
	    "BS",  "HT",  "LF",  "VT",  "FF",  "CR",  "SO",  "SI",
	    "DLE", "DC1", "DC2", "DC3", "DC4", "NAK", "SYN", "ETB",
	    "CAN", "EM",  "SUB", "ESC", "FS",  "GS",  "RS",  "US",
	    "SP"]

readLitChar            :: ReadS Char
readLitChar ('\\':s)    = readEsc s
 where
       readEsc ('a':s)  = [('\a',s)]
       readEsc ('b':s)  = [('\b',s)]
       readEsc ('f':s)  = [('\f',s)]
       readEsc ('n':s)  = [('\n',s)]
       readEsc ('r':s)  = [('\r',s)]
       readEsc ('t':s)  = [('\t',s)]
       readEsc ('v':s)  = [('\v',s)]
       readEsc ('\\':s) = [('\\',s)]
       readEsc ('"':s)  = [('"',s)]
       readEsc ('\'':s) = [('\'',s)]
       readEsc ('^':c:s) | c >= '@' && c <= '_'
			= [(toEnum (fromEnum c - fromEnum '@'), s)]
       readEsc s@(d:_) | isDigit d
			= [(toEnum n, t) | (n,t) <- readDec s]
       readEsc ('o':s)  = [(toEnum n, t) | (n,t) <- readOct s]
       readEsc ('x':s)  = [(toEnum n, t) | (n,t) <- readHex s]
       readEsc s@(c:_) | isUpper c
			= let table = ('\DEL',"DEL") : asciiTab
			  in case [(c,s') | (c, mne) <- table,
					    ([],s') <- [lexmatch mne s]]
			     of (pr:_) -> [pr]
				[]     -> []
       readEsc _        = []
readLitChar (c:s)       = [(c,s)]

showLitChar               :: Char -> ShowS
showLitChar c | c > '\DEL' = showChar '\\' .
			     protectEsc isDigit (shows (fromEnum c))
showLitChar '\DEL'         = showString "\\DEL"
showLitChar '\\'           = showString "\\\\"
showLitChar c | c >= ' '   = showChar c
showLitChar '\a'           = showString "\\a"
showLitChar '\b'           = showString "\\b"
showLitChar '\f'           = showString "\\f"
showLitChar '\n'           = showString "\\n"
showLitChar '\r'           = showString "\\r"
showLitChar '\t'           = showString "\\t"
showLitChar '\v'           = showString "\\v"
showLitChar '\SO'          = protectEsc ('H'==) (showString "\\SO")
showLitChar c              = showString ('\\' : snd (asciiTab!!fromEnum c))

protectEsc p f             = f . cont
 where cont s@(c:_) | p c  = "\\&" ++ s
       cont s              = s

-- Unsigned readers for various bases
readDec, readOct, readHex :: Integral a => ReadS a
readDec = readInt 10 isDigit    (\ d -> fromEnum d - fromEnum_0)
readOct = readInt  8 isOctDigit (\ d -> fromEnum d - fromEnum_0)
readHex = readInt 16 isHexDigit hex
	    where hex d = fromEnum d - (if isDigit d then fromEnum_0
				       else fromEnum (if isUpper d then 'A' else 'a') - 10)

fromEnum_0 :: Int
fromEnum_0 = fromEnum '0'

-- showInt is used for positive numbers only
showInt    :: Integral a => a -> ShowS
showInt n r | n < 0 = error "" --"Numeric.showInt: can't show negative numbers"
            | otherwise =
              let (n',d) = quotRem n 10
		  r'     = toEnum (fromEnum '0' + fromIntegral d) : r
	      in  if n' == 0 then r' else showInt n' r'

showSigned    :: Real a => (a -> ShowS) -> Int -> a -> ShowS
showSigned showPos p x = if x < 0 then showParen (p > 6)
						 (showChar '-' . showPos (-x))
				  else showPos x

-- readInt reads a string of digits using an arbitrary base.  
-- Leading minus signs must be handled elsewhere.

readInt :: Integral a => a -> (Char -> Bool) -> (Char -> Int) -> ReadS a
readInt radix isDig digToInt s =
    [(foldl1 (\n d -> n * radix + d) (map (fromIntegral . digToInt) ds), r)
	| (ds,r) <- nonnull isDig s ]

readSigned:: Real a => ReadS a -> ReadS a
readSigned readPos = readParen False read'
		     where read' r  = read'' r ++
				      [(-x,t) | ("-",s) <- lex r,
						(x,t)   <- read'' s]
			   read'' r = [(n,s)  | (str,s) <- lex r,
						(n,"")  <- readPos str]


-- This floating point reader uses a less restrictive syntax for floating
-- point than the Haskell lexer.  The `.' is optional.
readFloat     :: RealFrac a => ReadS a
readFloat r    = [(fromRational ((n%1)*10^^(k-d)),t) | (n,d,s) <- readFix r,
						       (k,t)   <- readExp s] ++
                 [ (0/0, t) | ("NaN",t)      <- lex r] ++
                 [ (1/0, t) | ("Infinity",t) <- lex r]
		 where readFix r = [(read (ds++ds'), length ds', t)
					| (ds, d) <- lexDigits r
                                        , (ds',t) <- lexFrac d   ]

                       lexFrac ('.':s) = lexDigits s
		       lexFrac s       = [("",s)]

		       readExp (e:s) | e `elem` "eE" = readExp' s
		       readExp s                     = [(0,s)]

		       readExp' ('-':s) = [(-k,t) | (k,t) <- readDec s]
		       readExp' ('+':s) = readDec s
		       readExp' s       = readDec s

-- Monadic I/O: --------------------------------------------------------------

--data IO a = IO a           -- builtin datatype of IO actions

-- data type describing IOErrors / exceptions.
{-data IOError
  = IOError
      { ioe_kind        :: IOErrorKind    -- what kind of (std) error
      , ioe_loc         :: String         -- location of the error
      , ioe_description :: String         -- error-specific string
      , ioe_fileName    :: (Maybe String) -- the resource involved.
      }
-}
      
data IOError = IOError IOErrorKind String String (Maybe String)

data IOErrorKind
  = IOError_UserError
  | IOError_IllegalError
  | IOError_PermDenied
  | IOError_AlreadyExists
  | IOError_AlreadyInUse
  | IOError_DoesNotExist
  | IOError_FullError
  | IOError_EOF
  | IOError_WriteError

instance Show IOErrorKind where
  show x =
    case x of
     IOError_UserError      -> "UE"--"User error"
     IOError_IllegalError   -> "IO"--"Illegal operation"
     IOError_PermDenied     -> "PD"--"Permission denied"
     IOError_AlreadyExists  -> "AE"--"Already exists"
     IOError_AlreadyInUse   -> "RB"--"Resource busy"
     IOError_DoesNotExist   -> "DNE"--"Does not exist"
     IOError_FullError      -> "RE"--"Resource exhausted"
     IOError_EOF            -> "EOF"--"End of file"
     IOError_WriteError	    -> "WE"--"Write error"
      	
{-
  Strange looking, but these defns are used in IO without
  exporting them from the Prelude (the interpreter makes the
  connection between the two under-the-hood...saves having
  to extend Prelude's export list in non-standard ways.
-}
{-
ioeGetErrorString__ :: IOError -> String
ioeGetErrorString__ ioe = 
  case ioe_kind ioe of
    IOError_UserError{} -> ioe_description ioe
    x -> show x

ioeGetFilename__ :: IOError -> Maybe String
ioeGetFilename__ ioe = ioe_fileName ioe
-}

instance Show IOError where
  showsPrec p (IOError kind loc descr mbFile) = 
    showString "IO Error: " . showsPrec p kind . 
    (case loc of
       "" -> id
       _  -> showString "\nAction: " . showString loc) .
      (case descr of
	 "" -> id
	 _  -> showString "\nReason: " . showString descr) .
      (case mbFile of
	 Nothing -> id
	 Just name -> showString "\nResource: " . showString name)

type FilePath = String  -- file pathnames are represented by strings

instance Show (IO a) where
    showsPrec p f = showString "IA"  --"<<IO action>>"

primbindIO :: IO a -> (a -> IO b) -> IO b
primbindIO (AProVE_IO x) f        = f x
primbindIO (AProVE_Exception y) f = AProVE_Exception y
primbindIO (AProVE_Error y)     f = AProVE_Error y

primretIO  :: a -> IO a
primretIO = AProVE_IO 

{-
catch      :: IO a -> (IOError -> IO a) -> IO a
catch (AProVE_IO x) f = (AProVE_IO x)
catch (AProVE_Exception (AET_IOError x)) f = f x
catch x             f = x 
-}

errorFrame :: IO a -> IO a
errorFrame (AProVE_IO x) = (AProVE_IO x)
errorFrame x             = x
errorFrame (AProVE_Error x) = AProVE_Exception (AET_MatchFailure "") -- ErrorResult PatternMatchFailure errorFrameRuleNumber 2 
errorFrame (AProVE_Error x) = AProVE_Exception (AET_ErrorCall x)     -- ErrorResult ErrorCall           errorFrameRuleNumber 3


catch      :: IO a -> (IOError -> IO a) -> IO a
catch x = pCatch (errorFrame x)

pCatch (AProVE_Exception (AET_IOError x)) f = f x
pCatch x                                  f = x


aIOE  :: IOErrorKind -> IO a
aIOE x = AProVE_Exception (AET_IOError (IOError x "" "" Nothing))


ioError    :: IOError -> IO a
ioError x = AProVE_Exception (AET_IOError x)

putChar    :: Char -> IO ()
putChar x = seq x (output)


output = randomSelect [aIOE IOError_FullError,
                       aIOE IOError_PermDenied,
                       AProVE_IO ()]

putStr     :: String -> IO ()
putStr  []    = output
putStr (x:xs) = (putChar x) >> putStr xs 

randomSelect :: [a] -> a 
randomSelect [x]                 = x
randomSelect (x:xs) | terminator = randomSelect xs 
                    | otherwise  = x

{-
primListEval :: [a] -> ()
primListEval     [] = ()
primListEval (x:xs) = seq x (primListEval xs)
-}

getChar    :: IO Char
getChar | terminator = return terminator 
        | otherwise  = aIOE IOError_EOF

-- needed locally.
isEOFError :: IOError -> Bool
isEOFError (IOError IOError_EOF _ _ _) = True
isEOFError _ = False

userError :: String -> IOError
userError str = IOError IOError_UserError "" str Nothing

print     :: Show a => a -> IO ()
print      = putStrLn . show

putStrLn  :: String -> IO ()
putStrLn s = do putStr s
		putChar '\n'

getLine :: IO String
getLine  = do {
  c <- getChar;
  if c=='\n'
   then return ""
   else do {
     ls <- getRest;
     return (c:ls) }}
  where
   getRest = do
     c <- catch getChar
                (\ ex -> if isEOFError ex then
			    return '\n'
			 else
			    ioError ex)
     if c=='\n'
      then return ""
      else do
       cs <- getRest
       return (c:cs)

-- raises an exception instead of an error
readIO          :: Read a => String -> IO a
readIO s         = case [x | (x,t) <- reads s, ("","") <- lex t] of
                        [x] -> return x
                        []  -> ioError (userError "NP")--"PreludeIO.readIO: no parse")
                        _   -> ioError (userError "AP")--"PreludeIO.readIO: ambiguous parse")

readLn          :: Read a => IO a
readLn           = do l <- getLine
                      r <- readIO l
                      return r

getContents 		 :: IO String
getContents | terminator = return []
            | otherwise  = do x  <- getChar 
                              xs <- getContents 
                              return (x:xs)

writeFile   		 :: FilePath -> String -> IO ()
writeFile f xs = putStr f >> putStr xs 

appendFile  		 :: FilePath -> String -> IO ()
appendFile f xs = putStr f >> putStr xs

readFile    		 :: FilePath -> IO String
readFile f = putStr f >> getContents 

interact  :: (String -> String) -> IO ()
interact f = getContents >>= (putStr . f)

instance Functor IO where
    fmap f x = x >>= (return . f)

instance Monad IO where
    (>>=)  = primbindIO
    return = primretIO

    fail s = ioError (userError s)

-- Hooks for primitives: -----------------------------------------------------
-- Do not mess with these!

--data FunPtr a -- builtin datatype of C function pointers
--data Ptr a    -- builtin datatype of C pointers
--data Addr     -- builtin datatype of C pointers (deprecated)
--data Word     -- builtin datatype of unsigned ints (deprecated)
--data Int8
--data Int16
--data Int32
--data Int64
--data Word8
---data Word16
---data Word32
---data Word64
---data ForeignObj  -- builtin datatype of C pointers with finalizers (deprecated)
---data ForeignPtr a -- builtin datatype of C pointers with finalizers
---data StablePtr a

data IO a = AProVE_IO a | AProVE_Exception AET | AProVE_Error String

data AET = AET_IOError IOError | AET_MatchFailure String | AET_ErrorCall String 

primCompAux      :: Ord a => a -> a -> Ordering -> Ordering
primCompAux x y o = case compare x y of EQ -> o; LT -> LT; GT -> GT

primPmInt        :: Num a => Int -> a -> Bool
primPmInt n x     = fromInt n == x

primPmInteger    :: Num a => Integer -> a -> Bool
primPmInteger n x = fromInteger n == x

primPmFlt        :: Fractional a => Double -> a -> Bool
primPmFlt n x     = fromDouble n == x

-- The following primitives are only needed if (n+k) patterns are enabled:
primPmNpk        :: Integral a => Int -> a -> Maybe a
primPmNpk n x     = if n'<=x then Just (x-n') else Nothing
		    where n' = fromInt n

primPmSub        :: Integral a => Int -> a -> a
primPmSub n x     = x - fromInt n

-- End of Hugs standard prelude ----------------------------------------------

default (Integer,Double)












-- This class is used for lazy termination analysis ---------------------------

class LazyTermination a where
	lazyTerminating :: Nat -> a -> Bool
	lazyGenerator :: a

instance (LazyTermination a, LazyTermination b) => LazyTermination (a -> b) where
	lazyTerminating Zero _ = True
	lazyTerminating (Succ n) f = lazyTerminating (Succ n) (f lazyGenerator)
	lazyGenerator x = (lazyTerminating terminator x) `seq` lazyGenerator
