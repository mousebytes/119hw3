-- Alfonso Morales : 301975025
import FLang
import Data.List

-- all strings in which every a is immediately followed by a bb
r = Star(Union(Let 'b') (Cat (Let 'a')(Cat (Let 'b')(Let 'b'))))




--helper function for str to regex
str_to_re::String->RegExp
str_to_re [] = Empty
str_to_re [c] = Let c
str_to_re (c:cs) = Cat (Let c) (str_to_re cs)


-- helper function for cahnging letters in regex
-- currently hard coded to replace a's with "aa" and b's with "bb"
s::Char -> String
s 'a' = "a"
s 'b' = "bb"

-- convert each char from a given regular expression then substitute it with a string
direct :: (Char -> String) -> RegExp -> RegExp
direct s (Let c) = str_to_re (s c)
direct s (Cat r1 r2) = Cat (direct s r1) (direct s r2)
direct s (Union r1 r2) = Union (direct s r1) (direct s r2)
direct s (Star r) = Star (direct s r)
direct _ Empty = Empty

-- r' is a regex with a substitution function "s" applied via function "direct"
r' = direct s r

{-
ghci> Compact r'
(bb+aabbbb)*
ghci> Compact r
(b+abb)*
-}


-- inverse must be as follows, at least how  i understand it
-- we are walking through the same machine BUT
-- we are using substitution to walk through it

inverse :: (Char -> String) -> FSM a -> FSM a
inverse s (qs,ss,fs,d) = (qs,ss,fs,d') where
    d' q c = step_through_string (qs,ss,fs,d) q (s c) -- send it fsm, cur state, string to create d' (s c means that it is sending our char,c,  to the s [substitution] function then it will be parsed by step_through_string)
    
-- testing purposes -> delete later (Along with the m1 towards the bottom)
inv = inverse s m1


{-
EX to explain inverse:

Say we had 
s 'a' = "ab"
s 'b' = "ba"

we send a machine, we'll say m1, with the delta function
    d 0 'b' = 0
    d 0 'a' = 1
    d 1 'a' = 4
    d 1 'b' = 2
    d 2 'a' = 4
    d 2 'b' = 3
    d 3 'b' = 3
    d 3 'a' = 1
    d 4 _ = 4

inverse s m1

If we're reading "ab" s(ab) = abba

We start at state 0, since it is the start state
0 on a -> 1
1 on b -> 2
2 on b -> 3
3 on a -> 1
-}

-- this function takes in an FSM of any type, any data type (state), a string, then returns any data type (state)
-- this is delta star from notes -> I Think ?
-- we're crafting the new transition function for inverse here
step_through_string:: (FSM a) -> a -> String -> a
step_through_string (_,_,_,d) startState str = foldl d startState str -- step through the string -> applying delta one letter at a time
-- then returjn the final state you end up in
    
    {-
    EX: 
    Say we had a transition function that looked like this:
    (FSM d For all a's followed by bb)
    d 0 'b' = 0
    d 0 'a' = 1
    d 1 'a' = 4
    d 1 'b' = 2
    d 2 'a' = 4
    d 2 'b' = 3
    d 3 'b' = 3
    d 3 'a' = 1
    d 4 _ = 4

    foldl d 0 "abb"
    d (d (d 0 'a') 'b') 'b'
    d (d 1 'b') 'b'
    d 2 'b'
    3
    so we'd end up at 3, which is correct since it's abb and that's a final state
    -}

m1::FSM Int
m1 = ([0,1,2,3,4], 0, [0,3], d) where
    d 0 'b' = 0
    d 0 'a' = 1
    d 1 'a' = 4
    d 1 'b' = 2
    d 2 'a' = 4
    d 2 'b' = 3
    d 3 'b' = 3
    d 3 'a' = 1
    d 4 _ = 4


--ws = ["b","bb"]

-- this Eq a=> was recommended by my IDE to fix the `elem` error -> ask wilson later
rightq :: Eq a => [String] -> FSM a -> FSM a -- Inputs -> our ws, an FSM -- Output -> FSM
rightq ws (qs,ss,fs,d) = (qs,ss,f',d) where -- qs,ss,d are the same, fs turns to f' via definition below (stolen from notes)
    f' = [q | q <- qs, any (\w -> step_through_string (qs,ss,fs,d) q w `elem` fs) ws] 
    -- loop through every state in fsm
    -- for every q cehck if there's any string, w, in ws where we land in a final state
        -- if that's true then put that state in as a final state in f'

    -- in greater detail:
    -- for every q in list qs, check the condition after the comma (every state in list of states from FSM)
    -- build a list of states using that condition, where the condition is
    -- any (\w -> ...) ws -> checks if at least one string makes the condition true
    -- \w ... -> \w just means that we're applying to every string in ws
    -- step_through_string is previously defined
    -- step_through_string (qs,ss,fs,d) q w is just running through na FSM using q as the start state and w as the string to run through
    -- something `elem` fs -> is asking is the something before `elem` a part of fs
    -- the backticks `elem` allow for the notation
    -- x 'elem' xs -> to be used
    -- in essence the entire function is building a list of new final states by checking 
    --if at least one string lands on a final state from each state
    





