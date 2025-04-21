module FLang where

import Data.List (sort, inits, tails, stripPrefix, foldl')
import Data.Array (Array, listArray, (!))

---------------- General list functions ---------------------------------------

-- Set difference
diff :: Eq a => [a] -> [a] -> [a]
diff xs ys = filter (\x -> notElem x ys) xs

-- Convert equivalence relation on a set to a partition
eq2part :: Eq a => [a] -> [(a,a)] -> [[a]]
eq2part as rs = blocks as where
  blocks [] = []
  blocks (a:as) = let b = eqclass a
                  in b : blocks (as `diff` b)
  eqclass x = [y | (x',y) <- rs, x == x']


-- Normalize a list: sort and remove duplicates
norm :: Ord a => [a] -> [a]
norm xs = rad $ sort xs where
  rad :: Eq a => [a] -> [a]  -- Remove adjacent duplicates
  rad [] = []
  rad [x] = [x]
  rad (x:ys@(y:zs)) | x == y = rad ys
                    | otherwise = x : rad ys

-- Cartesian product, preserves normalization
cart :: [a] -> [b] -> [(a,b)]
cart xs ys = [(x,y) | x <- xs, y <- ys]

-- Powerset, preserves normalization
power :: [a] -> [[a]]
power [] = [[]]
power (x:xs) = let ys = power xs
               in [] : map (x:) ys ++ tail ys

-- Check whether two lists overlap
overlap :: Eq a => [a] -> [a] -> Bool
overlap [] ys = False
overlap (x:xs) ys = elem x ys || overlap xs ys

-- splits xs = list of all possible splits of xs, in order. For example,
-- splits "abc" = [("","abc"), ("a","bc"), ("ab","c"), ("abc","")]
splits :: [a] -> [([a], [a])]
splits xs = zip (inits xs) (tails xs)

-- Unary set closure (where "set" = normalized list)
-- uclosure xs g == smallest set containing xs and closed under g
uclosure :: Ord a => [a] -> (a -> [a]) -> [a]
uclosure xs g = sort $ stable $ iterate close (xs, []) where
  stable ((fr,xs):rest) = if null fr then xs else stable rest
  close (fr, xs) = (fr', xs') where
    xs' = fr ++ xs
    fr' = norm $ filter (`notElem` xs') $ concatMap g fr


---------------- Length-ordered lists -----------------------------------------

-- Length-Ordered Lists over "character type" a (aka "strings")
-- Invariant: In LOL n xs, n == length xs
data LOL a = LOL Int [a] deriving (Eq,Ord)

-- Show instance doesn't print LOL constructor or length
instance Show a => Show (LOL a) where
  show (LOL n xs) = show xs

-- Empty list (epsilon)
eps :: LOL a
eps = LOL 0 []

-- Smart constructor for LOL a, establishes invariant
lol :: [a] -> LOL a
lol xs = LOL (length xs) xs

-- Concatenation of LOLs, preserves invariant
dot :: LOL a -> LOL a -> LOL a
dot xs (LOL 0 _) = xs                            -- special case, for efficiency
dot (LOL n xs) (LOL m ys) = LOL (n+m) (xs++ys)   -- general case


---------------- Languages ----------------------------------------------------

-- Fixed alphabet, but everything below should work for any sigma!
sigma :: [Char]
sigma = "ab"


-- Normalized lists of LOLs (aka "languages"), possibly infinite
-- Invariant: xs :: Lang a implies xs is sorted with no duplicates
type Lang a = [LOL a]


-- Smart constructor for (finite) languages, establishes invariant
lang :: Ord a => [[a]] -> Lang a
lang xs = norm $ map lol xs

-- Membership for languages (infinite lists satisfying invariant included)
memb :: Ord a => LOL a -> Lang a -> Bool
memb _ [] = False
memb x (y:ys) =
  case compare x y of
    LT -> False
    EQ -> True
    GT -> memb x ys
                           
-- Merge two sorted lists (aka "union")
merge :: Ord a => [a] -> [a] -> [a]
merge [] ys = ys
merge xs [] = xs
merge xs@(x:xr) ys@(y:yr) =
  case compare x y of
    LT -> x : merge xr ys
    EQ -> x : merge xr yr
    GT -> y : merge xs yr

-- Concatenation of languages
cat :: Ord a => Lang a -> Lang a -> Lang a
cat [] _ = []
cat _ [] = []
cat (x:xr) ys@(y:yr) = dot x y : merge (map (dot x) yr) (cat xr ys)

-- Kleene star of a language
kstar :: Ord a => Lang a -> Lang a
kstar [] = [eps]
kstar (LOL 0 []:xr) = kstar xr
kstar xs = eps : cat xs (kstar xs)


-- All strings of length <= n over sigma, in LOL order. Useful for testing
strings :: Int -> [String]
strings n = concat [strs i | i <- [0..n]] where
  strs 0 = [""]
  strs n = [a:xs | a <- sigma, xs <- strs (n-1)]



---- Regular Expressions ------------------------------------------------------

---- Traditional regular expressions
data RegExp = Empty                -- Empty language
            | Let Char             -- Single letter language
            | Union RegExp RegExp  -- Union
            | Cat RegExp RegExp    -- Concatenation
            | Star RegExp          -- Kleene star
            deriving (Show, Eq)

-- Compact display form for RegExp
newtype Compact = Compact RegExp

instance (Show Compact) where    -- use precedence to minimize parentheses
  showsPrec d (Compact r) = sp d r where
    sp d Empty         = showString "0"
    sp d (Let c)       = showString [c]
    sp d (Union r1 r2) = showParen (d > 6) $  -- prec(Union) = 6
                         sp 6 r1 .
                         showString "+" .
                         sp 6 r2
    sp d (Cat r1 r2)   = showParen (d > 7) $  -- prec(Cat) = 7
                         sp 7 r1 .
                         sp 7 r2
    sp d (Star Empty)  = showString "1"
    sp d (Star r1)     = sp 9 r1 .     -- prec(Star) = 8
                         showString "*"


-- Quick and dirty postfix RegExp parser, gives non-exaustive match on error
-- Allows 1 to be used as an input form for 0*
toRE :: String -> RegExp
toRE w = go w [] where
  go [] [r]              = r  -- must be only one RegExp on stack at the end
  go ('+':xs) (r2:r1:rs) = go xs (Union r1 r2:rs)
  go ('.':xs) (r2:r1:rs) = go xs (Cat r1 r2:rs)
  go ('*':xs) (r:rs)     = go xs (Star r:rs)
  go ('0':xs) rs         = go xs (Empty:rs)
  go ('1':xs) rs         = go xs (Star Empty:rs)
  go (x:xs) rs           = go xs (Let x:rs)   -- everything else is a letter


-- The language associated to (aka denotation of) a regular expression: [[r]]
lang_of :: RegExp -> Lang Char
lang_of Empty = []
lang_of (Let a) = lang [[a]]
lang_of (Union r1 r2) = merge (lang_of r1) (lang_of r2)
lang_of (Cat r1 r2) = cat (lang_of r1) (lang_of r2)
lang_of (Star r1) = kstar (lang_of r1)


-- The one-string and finite languages of Theorem 3.2.
onestr :: String -> RegExp
onestr [] = Star Empty
onestr [x] = Let x
onestr (x:xs) = Cat (Let x) (onestr xs)

finite :: [String] -> RegExp
finite [] = Empty
finite [w] = onestr w
finite (w:ws) = Union (onestr w) (finite ws)


---- Some recursive functions on regular expressions

-- Bypassable
byp :: RegExp -> Bool
byp Empty = False
byp (Let _) = False
byp (Union r1 r2) = byp r1 || byp r2
byp (Cat r1 r2) = byp r1 && byp r2
byp (Star r1) = True
  
-- Left quotient (by a letter)
lq :: Char -> RegExp -> RegExp
lq s Empty = Empty
lq s (Let c) = if s == c then Star Empty else Empty
lq s (Union r1 r2) = Union (lq s r1) (lq s r2)
lq s (Cat r1 r2) | byp r1 = Union (Cat (lq s r1) r2) (lq s r2)
                 | otherwise = Cat (lq s r1) r2
lq s (Star r1) = Cat (lq s r1) (Star r1)

-- Number of letters 
numLets :: RegExp -> Int
numLets Empty = 0
numLets (Let _) = 1
numLets (Union r1 r2) = numLets r1 + numLets r2
numLets (Cat r1 r2) = numLets r1 + numLets r2
numLets (Star r1) = numLets r1

-- Star height (depth of nested stars)
starHgt :: RegExp -> Int
starHgt Empty = 0
starHgt (Let _) = 0
starHgt (Union r1 r2) = starHgt r1 `max` starHgt r2
starHgt (Cat r1 r2) = starHgt r1 `max` starHgt r2
starHgt (Star r1) = 1 + starHgt r1

-- Matching algorithm 1
match1 :: RegExp -> String -> Bool
match1 Empty _ = False
match1 (Let c) w = w == [c]
match1 (Union r1 r2) w = match1 r1 w || match1 r2 w
match1 (Cat r1 r2) w = any (\(w1,w2) -> match1 r1 w1 && match1 r2 w2) (splits w)
match1 (Star r) w = null w ||
  any (\(w1,w2) -> match1 r w1 && match1 (Star r) w2) (tail $ splits w)

-- Matching algorithm 2
match2 :: RegExp -> String -> Bool
match2 r w = m [r] False w where
  m :: [RegExp] -> Bool -> String -> Bool  -- for c, False is 0, True is 1
  m [] c w = not c && null w
  m (Empty : rs) c w = False
  m (Let a : rs) c [] = False
  m (Let a : rs) c (x:xs) = a == x && m rs False xs
  m (Union r1 r2 : rs) c w = m (r1:rs) c w || m (r2:rs) c w
  m (Cat r1 r2 : rs) c w = m (r1:r2:rs) c w || c && byp r1 && m (r2:rs) c w
  m (Star r1 : rs) c w = not c && m rs c w || m (r1:Star r1:rs) True w


---- Extended regular expressions
data RegExp' = Zero | One | Let' Char |
               Union' [RegExp'] | Cat' [RegExp'] | Star' RegExp'
  deriving (Eq, Ord, Show)

-- Convert ordinary REs into extended REs
fromRE :: RegExp -> RegExp'
fromRE Empty = Zero
fromRE (Let c) = Let' c
fromRE (Union r1 r2) = Union' [fromRE r1, fromRE r2]
fromRE (Cat r1 r2) = Cat' [fromRE r1, fromRE r2]
fromRE (Star r1) = Star' (fromRE r1)

-- Convert extended REs into ordinary REs, eliminating Union' and Cat' on
-- lists of length < 2, and right-associating them on longer lists
fromRE' :: RegExp' -> RegExp
fromRE' Zero = Empty
fromRE' One = Star Empty
fromRE' (Let' c) = Let c
fromRE' (Union' []) = Empty
fromRE' (Union' [r]) = fromRE' r
fromRE' (Union' (r:rs)) = Union (fromRE' r) (fromRE' (Union' rs))
fromRE' (Cat' []) = Star Empty
fromRE' (Cat' [r]) = fromRE' r
fromRE' (Cat' (r:rs)) = Cat (fromRE' r) (fromRE' (Cat' rs))
fromRE' (Star' r) = Star (fromRE' r)

-- Bypassability for extended REs
byp' :: RegExp' -> Bool
byp' Zero = False
byp' One = True
byp' (Let' c) = False
byp' (Union' rs) = any byp' rs
byp' (Cat' rs) = all byp' rs
byp' (Star' r) = True

-- Left quotient for extended REs
lq' :: Char -> RegExp' -> RegExp'
lq' a Zero = Zero
lq' a One = Zero
lq' a (Let' c) = if a == c then One else Zero
lq' a (Union' rs) = Union' $ map (lq' a) rs
lq' a (Cat' rs) = Union' $ d rs where
  d [] = []
  d (r:rs) = Cat' (lq' a r : rs) : if byp' r then d rs else []
lq' a (Star' r) = Cat' [lq' a r, Star' r] 


---- Simplification of extended regular expressions
{-  A "simplified" RegExp' satisfies the following conditions:
(1) Every Union' is applied to a normalized list of two or more arguments,
    each of which is a One, Let', Cat', or Star' (i.e., not Zero or Union')
(2) Every Cat' is applied to a list of two or more arguments, each of which is
    a Let' or Star' (i.e., not Zero, One, Union', or Cat')
(3) Every Star' is applied to a Let', Union', or Cat' (i.e., not Zero, One,
    or Star')

The following simplification rules, when applied repeatedly at every subterm
of a RegExp' until it no longer changes, result in a simplified RegExp':

   Union' []                          --> Zero
   Union' [r]                         --> r
   Union' (rs1 ++ [Zero] ++ rs2)      --> Union' (rs1 ++ rs2)
   Union' (rs1 ++ [Union' rs] ++ rs2) --> Union' (rs1 ++ rs ++ rs2)
   Union' rs                          --> Union' (norm rs)                  (*)

   Cat' []                            --> One
   Cat' [r]                           --> r
   Cat' (rs1 ++ [Zero] ++ rs2)        --> Zero
   Cat' (rs1 ++ [One] ++ rs2)         --> Cat' (rs1 ++ rs2)
   Cat' (rs1 ++ [Union' rs] ++ rs2)   --> Union' (map f rs), where
                                          f r = Cat' (rs1 ++ [r] ++ rs2)
   Cat' (rs1 ++ [Cat' rs] ++ rs2)     --> Cat' (rs1 ++ rs ++ rs2)

   Star' Zero                         --> One
   Star' One                          --> One
   Star' (Star' r)                    --> Star' r

(*) Note: this rule should only be applied if rs is not already normalized;
    normalization is used to realize the commutativity and idempotency of union
    (i.e., that  L1 u L2 = L2 u L1  and  L u L = L ).

However, it would be very inefficient to attempt to apply these rules in the
manner indicated. Instead, we stage the application of these rules carefully
to minimize the number of traversals of the regular expression.               -}

simp :: RegExp' -> RegExp'
simp Zero = Zero
simp One = One
simp (Let' c) = Let' c
simp (Union' rs) = union' $ flat_uni $ map simp rs
simp (Cat' rs) = union' $ flat_cat $ map simp rs
simp (Star' r) = star' $ simp r

-- Smart constructor for Union' that normalizes its arguments and
-- handles the empty and singleton cases
union' :: [RegExp'] -> RegExp'
union' rs =  case norm rs of
  []  ->  Zero
  [r] -> r
  rs  -> Union' rs

-- Smart constructor for Cat' that handles the empty and singleton cases
cat' :: [RegExp'] -> RegExp'
cat' [] = One
cat' [r] = r
cat' rs = Cat' rs

-- Smart constructor for Star' that handles the constant and Star' cases
star' :: RegExp' -> RegExp'
star' Zero = One
star' One = One
star' (Star' r) = star' r
star' r = Star' r

-- Flatten a list of arguments to Union'; assumes each argument is simplified
flat_uni :: [RegExp'] -> [RegExp']
flat_uni [] = []
flat_uni (Zero:rs) = flat_uni rs
flat_uni (Union' rs':rs) = rs' ++ flat_uni rs
flat_uni (r:rs) = r : flat_uni rs

-- Flatten a list of arguments to Cat', turning them into a list of arguments
-- to Union'; assumes each argument is simplified
flat_cat :: [RegExp'] -> [RegExp']
flat_cat rs = fc [] rs where
  -- fc (args already processed, in reverse order) (args still to be processed)
  fc :: [RegExp'] -> [RegExp'] -> [RegExp']
  fc pr [] = [cat' $ reverse pr]
  fc pr (Zero:rs) = []
  fc pr (One:rs) = fc pr rs
  fc pr (Cat' rs':rs) = fc (reverse rs' ++ pr) rs
  fc pr (Union' rs':rs) = concat $ map (fc pr . (:rs)) rs'
  fc pr (r:rs) = fc (r:pr) rs



---- Finite State Machines ----------------------------------------------------

-- Finite state machines, indexed by the type of their states
-- M = (states, start, finals, transitions)  
type FSM a = ([a], a, [a], a -> Char -> a)

-- Generalized * construction for transition functions
star :: (a -> Char -> a) -> (a -> [Char] -> a)
star = foldl'

-- Two definitions of acceptance
accept1 :: Eq a => FSM a -> [Char] -> Bool
accept1 (_, s, fs, d) w = elem (star d s w) fs

accept2 :: Eq a => FSM a -> [Char] -> Bool
accept2 (_, s, fs, d) w = go s w where
  go q [] = elem q fs
  go q (a:w) = go (d q a) w

-- reachable m == the part of m that is reachable from the start state
reachable :: Ord a => FSM a -> FSM a
reachable (qs, s, fs, d) = (qs', s, fs', d) where
  qs' = uclosure [s] (\q -> map (d q) sigma)
  fs' = filter (`elem` fs) qs'


-- Nondeterministic FSMs, indexed by their type of state
-- Prerequisite: qs and ss are normalized and the output of d is normalized
-- M = (states, starts, finals, transitions)  
type NFSM a = ([a], [a], [a], a -> Char -> [a])

-- Hat construction for transition functions
hat :: Ord a => (a -> Char -> [a]) -> ([a] -> Char -> [a])
hat d xs a = norm $ concat [d q a | q <- xs]

-- nacc m w == m accepts the string w
nacc :: Ord a => NFSM a -> [Char] -> Bool
nacc (qs, ss, fs, d) w = overlap (star (hat d) ss w) fs

-- Easy conversion from FSM to NFSM
fsm_to_nfsm :: Eq a => FSM a -> NFSM a
fsm_to_nfsm (qs, s, fs, d) = (qs, [s], fs, d') where
  d' q a = [d q a]

-- Conversion from NFSM to FSM by the "subset construction"
nfsm_to_fsm :: Ord a => NFSM a -> FSM [a]
nfsm_to_fsm (qs, ss, fs, d) = (qs', ss, fs', hat d) where
  qs' = power qs
  fs' = [xs | xs <- qs', overlap xs fs]


-- Reverse FSM to a NFSM.
reverseFSM :: Eq a => FSM a -> NFSM a
reverseFSM (qs1, s1, fs1, d1) = (qs1, fs1, [s1], d) where
  d q a = [q' | q' <- qs1, d1 q' a == q]


-- Nondeterministic FSMs with epsilon moves, indexed by their type of state
-- qs and ss are normalized and the output of d is normalized
-- M = (states, starts, finals, transitions, epsilon-moves)
type EFSM a = ([a], [a], [a], a -> Char -> [a], [(a,a)])

-- Eliminate epsilon moves
elim_eps :: Ord a => EFSM a -> NFSM a
elim_eps (qs, ss, fs, d, es) = (qs, eclose ss, fs, de) where
  eclose qs = uclosure qs (\q -> [q2 | (q1,q2) <- es, q1 == q])
  de q a = eclose (d q a)
  

-- Intify: Change the states of an FSM from an equality type to Int,
-- and use an array lookup for the transition function
intify :: Eq a => FSM a -> FSM Int
intify (qs, s, fs, d) = ([0..n-1], s', fs', d') where
  n = length qs
  m = length sigma
  s'  = ind qs s
  fs' = map (ind qs) fs
  arr = listArray ((0,0), (n-1,m-1)) [ind qs (d q a) | q <- qs, a <- sigma]
  d' q a = arr ! (q, ind sigma a)
  ind (q':qs) q = if q == q' then 0 else 1 + ind qs q



---- Conversions from RegExp to FSM, NFSM, and EFSM ---------------------------

-- Thompson construction
thompson :: RegExp -> EFSM Int
thompson r = ([0..n-1], ss, fs, d, es) where
  (n, ss, fs, d, es) = build r 0

  -- build r k returns (n, ss, fs, d, es), where ([k..n-1], ss, fs, d, es) is
  -- an EFSM that recognizes the same language as r.
  build Empty k = (k, [], [], undefined, [])
  build (Let c) k = (k+2, [k], [k+1], d, []) where
    d q a = if q == k && a == c then [k+1] else []
  build (Union r1 r2) k = (n2, ss1 ++ ss2, fs1 ++ fs2, d, es1 ++ es2) where
    (n1, ss1, fs1, d1, es1) = build r1 k
    (n2, ss2, fs2, d2, es2) = build r2 n1
    d q a = if q < n1 then d1 q a else d2 q a 
  build (Cat r1 r2) k = (n2, ss, fs2, d, es) where
    (n1, ss1, fs1, d1, es1) = build r1 k
    (n2, ss2, fs2, d2, es2) = build r2 n1
    ss = if byp r1 then ss1 ++ ss2 else ss1
    d q a = if q < n1 then d1 q a else d2 q a 
    es = es1 ++ cart fs1 ss2 ++ es2 
  build (Star r1) k = (n1, [k], [k], d, es) where
    (n1, ss1, fs1, d1, es1) = build r1 (k+1)
    d q a = if q == k then [] else d1 q a
    es = cart [k] ss1 ++ es1 ++ cart fs1 [k]

-- Glushkov construction
glushkov :: RegExp -> NFSM Int
glushkov r = ([0..n], ss, [n], d) where
  n = numLets r
  (0, ss, d) = rcat r n [n] empty  -- start from state n and end at 0
  empty _ _ = []
  -- Assuming M = ([j..n], ss, [n], d) is an NFSM, rcat r j ss d returns
  -- (i, ss', d'), where ([i..n], ss', [n], d') is an NFSM that accepts
  -- the language [[r]] . L(M), i.e., the "concatenation" of r and M.
  rcat Empty j ss d = (j, [], empty)
  rcat (Let c) j ss d = (i, [i], d') where
    i = j - 1  -- add one state for each letter
    d' q a = if q == i && a == c then ss else d q a
  rcat (Union r1 r2) j ss d = (n1, merge ss1 ss2, d') where
    (n2, ss2, d2) = rcat r2 j ss d
    (n1, ss1, d1) = rcat r1 n2 ss d
    d' q a = if q < n2 then d1 q a else d2 q a
  rcat (Cat r1 r2) j ss d = (n1, ss1, d') where
    (n2, ss2, d2) = rcat r2 j ss d
    (n1, ss1, d1) = rcat r1 n2 ss2 d2
    d' q a = if q < n2 then d1 q a else d2 q a
  rcat (Star r1) j ss d = (n1, ss', d1) where
    (n1, ss1, d1) = rcat r1 j ss' d  -- notice the loops here on ss1
    ss' = merge ss1 ss

-- Brzozowski construction (using extended regular expressions)
brzozowski :: RegExp' -> FSM RegExp'
brzozowski r = (qs, s, fs, d) where
  qs = uclosure [s] (\r -> [d r a | a <- sigma])
  s  = simp r
  fs = filter byp' qs
  d r a = simp $ lq' a r


---- Conversion from FSM to RegExp' -------------------------------------------

-- Solve a system of proper linear equations (see Sect. 6.1 - 6.2 of my notes)
solve :: [[RegExp']] -> [RegExp'] -> [RegExp']

solve [] [] = []
solve ((l11:l1J) : rows) (l1':lI') = simp x1 : xI where
  -- l11 is the corner element, and l1J = [l12,...,l1n] is the rest of 1st row
  -- rows are the rest of the rows [[l21,...,l2n], ..., [ln1,...,lnn]]
  -- l1' is the first constant
  -- lI' are the rest of the contants [l2',...,ln']
  
  -- first column [l21, ..., ln1]
  lI1 = map head rows

  -- sub-matrix [[l22,...,l2n], ..., [ln2,...,lnn]]
  lIJ = map tail rows   

  -- [[l22_bar,...,l2n_bar], ..., [ln2_bar,...,lnn_bar]] computed via (6)
  lIJ_bar = zipWith sixes lI1 lIJ            -- loops for i = 2 .. n
  sixes li1 liJ = zipWith (six li1) l1J liJ  -- loops for j = 2 .. n
  six li1 l1j lij = Union' [Cat' [li1, Star' l11, l1j], lij]

  -- [l2'_bar,..., ln'_bar] computed via (7)
  lI'_bar = zipWith seven lI1 lI'
  seven li1 li' = Union' [Cat' [li1, Star' l11, l1'], li']
    
  -- recursively solve the system of size n-1
  xI = solve lIJ_bar lI'_bar

  -- compute x1 from xI via (5)
  x1 = Cat' [Star' l11, Union' $ l1':zipWith (\lij xi -> Cat' [lij,xi]) l1J xI]


-- Convert FSM to RegExp'
fsm_to_re' :: Eq a => FSM a -> RegExp'
fsm_to_re' (qs, s, fs, d) = solution !! index s qs where
  coef q1 q2 = union' [Let' a | a <- sigma, d q1 a == q2]
  final q = if elem q fs then One else Zero
  solution = solve [[coef q1 q2 | q2 <- qs] | q1 <- qs] [final q | q <- qs]
  index x (y:ys) | x == y = 0
                 | otherwise = 1 + index x ys


---- FSM Minimization ---------------------------------------------------------

-- Machine that accepts the `op` of the languages accepted by m1 and m2
opFSM :: (Eq a, Eq b) => (Bool -> Bool -> Bool) -> FSM a -> FSM b -> FSM (a, b)
opFSM op (qs1, s1, fs1, d1) (qs2, s2, fs2, d2) = (qs, s, fs, d) where
  qs = cart qs1 qs2
  s  = (s1, s2)
  fs = [q | q@(q1,q2) <- qs, (q1 `elem` fs1) `op` (q2 `elem` fs2)]
  d (q1, q2) a = (d1 q1 a, d2 q2 a)

-- Reachable states of a NFSM
nreach :: Ord a => NFSM a -> [a]
nreach (qs, ss, fs, d) = uclosure ss (\q -> concat $ map (d q) sigma)

minimize :: Ord a => FSM a -> FSM [a]
minimize m@(qs1, s1, fs1, d1) = (qs, s, fs, d) where
  qs = eq2part qs1 $ diff (cart qs1 qs1) $ nreach $ reverseFSM $ opFSM (/=) m m
  s = block s1
  fs = [q | q <- qs, head q `elem` fs1]
  d q a = block $ d1 (head q) a
  block q = go qs where
    go (x:xs) = if q `elem` x then x else go xs




