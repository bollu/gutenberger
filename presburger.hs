{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
import qualified Data.Set as S
import Data.Bits

data NFA a where
    NFA :: (Ord s, Show s)  => S.Set s -- ^ universe: su
      -> (S.Set s) -- ^ initial: si
      -> (S.Set s) -- ^ final: sf
      -> (a -> s -> S.Set s) -- ^ transition: t
      -> NFA a

data DFA a where
    DFA :: (Ord s, Show s) => S.Set s -- ^ universe: su
     -> (S.Set s)  -- ^ initial: si
     -> (S.Set s)  -- ^ final: sf
     -> (a -> s -> s)  -- ^ transition: t
     -> DFA a

-- | Directly make the DFA work on the powerset space of the NFA
nfa2dfa :: NFA a -> DFA a
nfa2dfa (NFA su si sf t) = DFA su' (S.singleton si) sf' t' where
    su' = S.powerSet su
    t' = nondet t
    -- | Any subset of the powerset that has a final state
    -- is a final state
    sf' = S.filter (intersects sf) su'


-- | Trivially embed a DFA as an NFA
dfa2nfa :: DFA a -> NFA a
dfa2nfa (DFA su si sf t) = NFA su si sf t'
  where t' = \a s -> S.singleton $ t a s


-- | Remove unreachable states from the DFA after a fixed
-- number of steps for a given alphabet.
-- Note that for us, number of steps = max bit-width
-- and alphabet should usually be all bitstrings that have variables
-- we care about toggled.
dfaRemoveUnreachableAfterN :: Int -- ^ number of steps
                     -> S.Set a -- ^ alphabet
                     -> DFA a
                     -> DFA a
dfaRemoveUnreachableAfterN n as (DFA su si sf t) =
    let next ss = (foldMap (\s -> (S.map (`t` s) as)) ss) `S.union` ss
        reached i ss = if i == 0 then ss else reached (i-1) (next ss)
        unreached = su S.\\ reached n si
    in (DFA (su S.\\ unreached) si (sf S.\\ unreached) t)


-- https://en.wikipedia.org/wiki/DFA_minimization#Hopcroft's_algorithm
{-
dfaRefinePartition :: S.Set a -- ^ Alphabet
  -> (s -> a -> s) -- transition
  -> S.Set s -- universe (U)
  -> S.Set (S.Set s) -- partition (P)
  -> [(S.Set s)] -- worklist (W)
  -> (S.Set (S.Set s)) -- new parittion
dfaRefinePartition as t su p [] = p
dfaRefinePartition as t p (w:ws) =
    -- | Find all precessors to ss on alphabet s
    let pred a ss = S.filter (\s -> S.member (t s u) ss) su
    in reverse foldMap as $ \a ->
        let predW = pred a w
-}

-- | Minimal dfa for a given alphabet after n steps
dfaMinimalAfterN :: Int -> S.Set a -> DFA a -> DFA a
dfaMinimalAfterN = dfaRemoveUnreachableAfterN

-- | nfa reversal
-- To transition, apply the transition map on the universe,
-- and keep all the sets that reach the current set. This is
-- effectively a nfaReverse of the NFA transition, since we now return
-- all sets that _enter_ the current set.
nfaReverse :: NFA a -> NFA a
nfaReverse (NFA su si sf t) =
    NFA su sf si $ \a s -> S.filter (S.member s . t a) su

-- | NFA that accepts all states
univ :: NFA a
univ = let su = S.singleton () in NFA su su su (\ _ _ -> su)

-- | NFA that accepts no state
empty :: NFA a
empty = let su = S.singleton () in NFA su su S.empty (\ _ _ -> su)

-- | Return the state space, # of initial states, # of final states
nfaStateSpaceCard :: NFA a -> (Int, Int, Int)
nfaStateSpaceCard (NFA su si sf _) = (S.size su, S.size si, S.size sf)


dfaStateSpaceCard :: DFA a -> (Int, Int, Int)
dfaStateSpaceCard (DFA su si sf _) = (S.size su, S.size si, S.size sf)


debugNFA :: NFA a -> IO ()
debugNFA (NFA su si sf t) = do
    putStrLn $ "univ: " <> show su
    putStrLn $ "initial: " <> show su
    putStrLn $ "final: " <> show su

debugDFA :: DFA a -> IO ()
debugDFA (DFA su si sf t) = do
    putStrLn $ "univ: " <> show su
    putStrLn $ "initial: " <> show su
    putStrLn $ "final: " <> show su

-- | Disjoint union of two sets
disjointUnion :: (Ord a, Ord b) =>
    S.Set a -> S.Set b -> S.Set (Either a b)
disjointUnion sl sr =
  S.mapMonotonic Left sl <> S.mapMonotonic Right sr

-- | Accepts union of two languages
nfaUnion :: NFA a -> NFA a -> NFA a
nfaUnion (NFA su si sf t) (NFA su' si' sf' t') =
  NFA (disjointUnion su su')
      (disjointUnion si si')
      (disjointUnion sf sf')
      (\a s -> case s of
                Left l -> S.mapMonotonic Left  (t a l)
                Right r -> S.mapMonotonic Right (t' a r))

-- | Accepts intersection of two languages
nfaIntersection :: NFA a -> NFA a -> NFA a
nfaIntersection (NFA su si sf t) (NFA su' si' sf' t') =
  NFA (S.cartesianProduct su su')
      (S.cartesianProduct si si')
      (S.cartesianProduct sf sf')
      (\a (s, s') -> S.cartesianProduct (t a s) (t' a s'))

-- | Complement of DFA
dfaComplement :: DFA a -> DFA a
dfaComplement (DFA su si sf t) = DFA su si (su S.\\ sf) t


-- | Accepts complement of a language
-- Come up with an intuitive explanation for why just flipping
-- the final states does *not* cut it for an NFA
nfaComplement :: NFA a -> NFA a
nfaComplement = dfa2nfa . dfaComplement . nfa2dfa

-- | Perform a non-deterministic step of the NFA
nondet :: Ord s => (a -> s -> S.Set s) -> a -> S.Set s -> S.Set s
nondet f a s = foldMap (f a) s



-- | Run multiple steps of the NFA
nondetSequence :: Ord s => Foldable g  => (a -> s -> S.Set s) -> g a -> S.Set s -> S.Set s
nondetSequence f aa ss = foldr (nondet f) ss aa


-- | Check if two sets have non-empty intersection
intersects :: Ord s => S.Set s -> S.Set s -> Bool
intersects xs ys = not $ S.null $ S.intersection xs ys


transitiveClosure :: (Eq s, Ord s) =>
    (S.Set s -> S.Set s) -> (S.Set s ->  S.Set s)
transitiveClosure f a =
    let a' = f a
     in if a == a' then a else (transitiveClosure f a') `S.union` a


-- | All possible states visited from given alphabet set
-- and initial states
visitedAlphabet :: (Ord s, Ord a) =>
    (a -> s -> S.Set s) -- ^ transition relation
    -> S.Set a -- ^ alphabet
    -> S.Set s -- ^ Initial state
    -> S.Set s -- ^ all reachable states
visitedAlphabet t as =
  -- | All possible transitions from all possible sets
  let next ss = foldMap (\s -> foldMap (`t` s) as) ss
  in transitiveClosure $ \ss -> next ss `S.union` ss


visitedAlphabetN :: (Ord s, Ord a) => (a -> s -> S.Set s) -- transition relation
 -> Int -- ^ number of steps
 -> S.Set a -- ^ alphabet
 -> S.Set s -- ^ initial state
 -> S.Set s -- ^ all reachable states
visitedAlphabetN t 0 _ si = si
visitedAlphabetN t n as si =
  -- | All possible transitions from all possible sets
  let si' = foldMap (\s -> foldMap (`t` s) as) si
   in visitedAlphabetN t (n-1) as si'

-- | Check whether NFA accepts
runNFA :: NFA a -> [a] -> Bool
runNFA (NFA _ si sf t) aa = intersects (nondetSequence t aa si) sf

-- | Now encode PA as NFAs

-- | Key for the variable: ith variable is natural number i.
type Var = Int

-- | Bitvector.
newtype BV = BV Int deriving(Eq, Ord, Show, Bits)

(.!.) :: BV -> Int -> Bool
(.!.) (BV bv) ix = testBit bv ix

-- | Given indeces, create powerset of bitvectors with those indeces toggled
bvPowerSet :: S.Set Int -> S.Set BV
bvPowerSet ixs =
    S.mapMonotonic (\setIx -> foldl (\bv ix -> bv `setBit` ix) (BV 0) setIx)
    (S.powerSet ixs)

-- | Common boolean sets.
sb, sf, st :: S.Set Bool
sb = S.fromDistinctAscList [False, True]
st = S.singleton True
sf = S.singleton False

-- | half adder
half :: Bool  -> Bool
  -> (Bool, Bool) -- ^ (result, overflow)
half x y = (x `xor` y, x && y)

-- | full adder
full :: Bool -> Bool -> Bool
     -> (Bool, Bool) -- ^ (Result, Overflow)
full x y z =
    let (r, o) = half x y
        (r', o') = half r z
    in (r', o || o')

-- | Return emptyset if predicate is false,
-- and singleton if predicate is true
predicated :: Bool -> a -> S.Set a
predicated False _ = S.empty
predicated True a = S.singleton a

-- | i + j == k
-- NFA takes a bitvector as input, the bitvector fed at the ith timestep
-- is the ith slice of bits of all inputs.
-- eg, to check the constraint
-- x0 + x1 == x2 where (x0=3, x1=5, x2=9)
--
-- 1 1 0 0    3
-- 1 0 1 0    5
-- 1 0 0 1    8
--
--- the inputs fed as bitvectors are the *columns*:
-- [ BV (1, 1, 1), BV (1, 0, 0), BV (0, 1, 0), BV (0, 0, 1)]
-- Check if the bitvector has the correct value of the result. If
-- it does, store the carry. If it does not, quit to the empty state.
-- Note that this is deterministic and can be
-- a DFA by having a dedicated "fail state".
-- Initial and final states have zero carry.
add :: Var -> Var -> Var -> NFA BV
add i j k = NFA sb sf sf step where
    step v c =
        let (r, c') = full (v .!. i) (v .!. j) c
        in predicated ((v .!. k) == r) c'

-- | Check if two variables are equal
eq :: Var -> Var -> NFA BV
eq i k = let
   su = S.singleton ()
   in NFA su su su $ \v _ ->
        if ((v .!. i) == (v .!. k)) then su else S.empty

-- | Create an NFA for:  exists x. P x
-- find all states reachable from the state where i is enabled
-- (and also from 0, why??)
exists :: Var -> NFA BV -> NFA BV
exists i (NFA su si sf t) =
  let si' = visitedAlphabet t (S.fromList [BV 0, BV (bit i)]) si
      t' v s = t v s `S.union` t (setBit v i) s
  in NFA su si' sf t'

-- | Create an NFA for: forall x. P x
-- Encode this as not (exists x. not (P x))
forall :: Var -> NFA BV -> NFA BV
forall i = nfaComplement . exists i . nfaComplement

-- | Check if NFA language accepts the empty string
acceptsEmpty :: NFA a -> Bool
acceptsEmpty (NFA su si sf t) = intersects si sf

-- | forall x. forall y. eq x y
-- acceptsEmpty eg1 =  False
eg1 = forall 1 $ forall  0 $ eq 0 1


-- | Same as eg1, but with minmize in between
eg1' =
    let minimize = nfaMinimalAfterN 64 (bvPowerSet $ S.fromList $ [0..1])
     in minimize $ forall 1 $ minimize $ forall 0 $ eq 0 1


-- | forall x. exists y. eq x y
-- acceptsEmpty eg2 = true
eg2 = forall 1 $ exists  0 $ eq 0 1


-- | exists x. forall y. eq x y
-- acceptsEmpty eg2 = false
eg3 = exists 1 $ forall  0 $ eq 0 1

assert_ :: Bool -> String -> IO ()
assert_ True _ = pure ()
assert_ False s = error $ "failed check: " <> s

main :: IO ()
main = do
    assert_ (acceptsEmpty eg1 == False) "eg1"
    assert_ (acceptsEmpty eg2 == True) "eg2"
    assert_ (acceptsEmpty eg3 == False) "eg3"
    putStrLn $ "presburger"

nfaComplement' :: Int  -- ^ Number of steps
               -> S.Set a --  ^ Alphabet
               -> NFA a
               -> NFA a
nfaComplement' n as =
  dfa2nfa . dfaMinimalAfterN n as . dfaComplement  . nfa2dfa


nfaMinimalAfterN :: Ord a => Int -> S.Set a -> NFA a -> NFA a
nfaMinimalAfterN n as (NFA su si sf t) =
    let reached = visitedAlphabetN t n as si
    in NFA (S.intersection su reached) si (S.intersection sf reached) t

