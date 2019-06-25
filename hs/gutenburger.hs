{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}

import qualified Data.Set as S
import Data.Bits
import Data.Monoid
import Test.QuickCheck
import GHC.TypeLits
import Data.Proxy

--- Automata theory: An algorithmic approach
--  https://www7.in.tum.de/~esparza/autoskript.pdf
--      - Chapter 10: Applications III - Pr arithmetic

-- | floor division. 3/2 = 1, (-3)/2 = -2
(//) :: Integral a => a -> a -> a
(//) =  div


-- | bit-width
type Width = Int


-- | number of steps we will transition
type Steps = Int

data NFA a where
    NFA :: (Ord s, Show s)  => S.Set s -- ^ Univ: su
      -> (S.Set s) -- ^ initial: si
      -> (S.Set s) -- ^ final: sf
      -> (a -> s -> S.Set s) -- ^ transition: t
      -> NFA a

data DFA a where
    DFA :: (Ord s, Show s) => S.Set s -- ^ Univ: su
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
dfaRemoveUnreachableAfterN :: Steps -- ^ number of steps
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
  -> S.Set s -- Univ (U)
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
-- To transition, apply the transition map on the Univ,
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
    putStrLn $ "initial: " <> show si
    putStrLn $ "final: " <> show sf

debugDFA :: DFA a -> IO ()
debugDFA (DFA su si sf t) = do
    putStrLn $ "univ: " <> show su
    putStrLn $ "initial: " <> show si
    putStrLn $ "final: " <> show sf

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
nondetSequence f aa ss = foldl (flip $ nondet f) ss aa


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
 -> Steps -- ^ number of steps
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
-- runNFA (NFA _ si sf t) aa = intersects (nondetSequence t aa si) sf
runNFA (NFA _ si sf t) as =
    -- go :: [a] -> S.Set s -> S.Set s
    let go [] ss = ss
        go (a:as) ss = go as (foldMap (t a) ss)
    in intersects sf (go as si)
                         --
-- | Check whether the DF-- A accepts
runDFA :: DFA a -> [a] ->  Bool
-- runDFA dfa as = runNFA--  (dfa2nfa dfa) as
runDFA (DFA su si sf t) as =
    -- go :: [a] -> S.Set s -> S.Set s
    let go [] ss = ss
        go (a:as) ss = go as (S.map (t a) ss)
    in intersects sf (go as si)
--
-- | Now encode PA as NFAs

-- | Key for the variable: ith variable is N number i.
type Var = Int

-- | Bitvector.
newtype BV = BV Int deriving(Eq, Ord, Show, Bits)

-- Infix testBit.
(.!.) :: BV -> Int -> Bool
(.!.) (BV bv) ix = testBit bv ix

-- | little endian: 0th bit goes to least positoin
-- eg. False False True --> 1 0 0
-- eg. True False False --> 0 0 1
-- invariant: (toBV bs .!. ix) == bs !! ix
toBV :: [Bool] -> BV
toBV bs = BV $ sum $ zipWith (\b ix -> if b then shiftL 1 ix else 0) bs [0,1..]


-- | QuickCheck for toBV
qcToBV :: ListMaxSized 32 Bool -> Bool
qcToBV (ListMaxSized bs) =
  let ixs = [0..(length bs) - 1]
  in getAll $ mconcat $ map All $ map (\ix -> toBV bs .!. ix == bs !! ix) ixs

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
nfaAcceptsEmpty :: NFA a -> Bool
nfaAcceptsEmpty (NFA su si sf t) = intersects si sf


-- | Check if the DFA accepts the empty string
dfaAcceptsEmpty :: DFA a -> Bool
dfaAcceptsEmpty (DFA su si sf t) = intersects si sf


-- | Remove states from the NFA that are unreachable after N steps
nfaRemoveUnreachableAfterN :: Ord a => Int -> S.Set a -> NFA a -> NFA a
nfaRemoveUnreachableAfterN n as (NFA su si sf t) =
    let reached = visitedAlphabetN t n as si
    in NFA (S.intersection su reached) si (S.intersection sf reached) t

-- | Create the minimal DFA from the NFA after pruning with respect to steps and alphabet
nfa2dfaMinimalAfterN :: Ord a => Steps -> S.Set a -> NFA a -> DFA a
nfa2dfaMinimalAfterN n as nfa = minimalDFA as . nfa2dfa . nfaRemoveUnreachableAfterN  n as $ nfa

-- ^ State for hopcroft algorithm
data H a s = H {
  hp :: S.Set (S.Set s) -- ^ partitions
  , hw :: S.Set (S.Set s) -- ^ worklist
  , hu :: S.Set s -- ^ Univ set
  , ha :: S.Set a -- ^ alphabet
  , ht :: (a -> s -> s) -- ^ transition relation
}


-- | Refine a set with respect to another set
refineWrt :: Ord s => S.Set s -- ^ Y: to be refined
  -> S.Set s -- ^ X: To refine with
  -> (S.Set s, S.Set s) -- ^ refinement: (Y/X, Y \cap X)
refineWrt y x = (y S.\\ x, y `S.intersection` x)


-- | Replace the element a with [a]
replaceSetElem ::  Ord a => a -> [a] -> S.Set a -> S.Set a
replaceSetElem a as s = S.union (S.fromList as) (S.delete a s)

-- | Insert a set into the parititon. If the full set exists, then
-- refine it in the worklist. Otherwise, add the smaller set
insertRefinedIntoWorklist ::
  Ord s => S.Set s -- ^ Y: set that was refined
        -> (S.Set s, S.Set s) -- ^ refinement of Y
        -> Endo (H a s)
insertRefinedIntoWorklist y (y1, y2)  = Endo $ \h ->
  let wHasY = S.member y (hw h)
      ysmall = if S.size y1 < S.size y2 then y1 else y2
  in if wHasY
    then
        -- | Worklist has Y, replace it
        h { hw = replaceSetElem y [y1, y2] (hw h)}
    else
        -- | Insert smaller set into the worklist to ensure n (log n)
        h {hw = ysmall `S.insert` (hw h)   }

-- | Insert the partition into P, the set of partitions
insertRefinedIntoPartition :: Ord s =>
    S.Set s -- ^ the full set Y
    -> (S.Set s, S.Set s) -- ^ the refinement of y
    -> Endo (H a s)
insertRefinedIntoPartition y (y1, y2) = Endo $ \h ->
    h { hp = replaceSetElem y [y1, y2] (hp h) }


-- | Perform computation for each character
forEachCharacter :: (a -> Endo (H a s)) -> Endo (H a s)
forEachCharacter f = Endo $ \h -> runEndo h $ foldMap f (ha h)


-- | For each set that is reverse-reachable from a transition over a
-- given set. That is, provide all sets s' such that \exists c. s' -c-> s
forEachRevTransition :: (Ord s, Eq s) =>
    S.Set s  -- ^ Set to reverse-reach with: A
    -> (S.Set s -- ^ Set that is reverse reachable from A for some character c
        -> Endo (H a s))
    -> Endo (H a s)
forEachRevTransition a f =
  forEachCharacter $ \c ->
    Endo $ \h ->
        -- | get set of states that reach A with character C
        let x = revTransition (ht h) (hu h) a c
        in runEndo h $ f x

-- | Perform computation for each partition
forEachPartition :: (S.Set s -> Endo (H a s)) -> Endo (H a s)
forEachPartition f = Endo $ \h -> runEndo h $ foldMap f (hp h)


-- | A guard for monoids
guardMonoid :: Monoid m => Bool -> m -> m
guardMonoid False _ = mempty
guardMonoid True m = m

-- | Reverse transition relation
revTransition :: (Ord s, Eq s) => (a -> s -> s) -- ^ transition
  -> S.Set s -- ^ Univ
  -> S.Set s -- ^ set to enter into
  -> a -- ^ character to transition on
  -> S.Set s -- ^ reversed transition: returns all sets such that on transition enters into the given set
revTransition t su ss a = S.filter (\s -> (t a s) `S.member` ss ) su

-- | Take the first element from the worklist if posssible

-- | For each refined partiion
forEachRefinedPartition ::
  Ord s
  => S.Set s -- ^ set to refine against: x
  -> ((S.Set s, S.Set s)  -- ^ partitions: (y1 = y / x, y2 = y \cap x)
      -> S.Set s  -- ^ full set (y: y1 U y2)
      -> Endo (H a s)) -- ^ computation on partitions
  -> Endo (H a s)
forEachRefinedPartition x f =
    forEachPartition $
       \y -> let (y1, y2) = y `refineWrt` x
              in f (y1, y2) y

-- | Combinator to run an Endo computation
runEndo :: a -> Endo a -> a
runEndo a f = appEndo f a

-- | Perform a computation for each element in the worklist
takeWorklist :: (S.Set s -> Endo (H a s)) -> Endo (H a s)
takeWorklist f = Endo $ \h ->
    if null (hw h)
    then h
    else let h' = h { hw = S.drop 1 (hw h) }
             work =  (S.elemAt 0  (hw h))
          in runEndo h' $ (f work)

-- | https://en.wikipedia.org/wiki/DFA_minimization#Hopcroft's_algorithm
refineStep :: Ord s => Endo (H a s)
refineStep =
     -- | take the tip from the worklist
    takeWorklist $ \a ->
        -- | for each set that is reverse-reachable from 'a' by a transition:
        forEachRevTransition a $ \x ->
            -- | Refine every set that we have by X, and add the new set
            -- into the worklist and the parittion st
            forEachRefinedPartition x $ \(y1, y2) y ->
                -- ensure that neither partition is trivial
                (guardMonoid ((not . S.null $  y1) && (not . S.null $ y2)) $
                   -- | Insert the refined set into the partiiton and into
                   -- the worklist, and then pull more from the worklist
                   (insertRefinedIntoPartition y (y1, y2) <>
                   insertRefinedIntoWorklist y (y1, y2)) <>
                -- | Repeat the refinement
                refineStep)


-- | Extract the minimal DFA from the Hopcroft.
minimalDFA :: S.Set a -- ^ alphabet
           -> DFA a -- DFA to minimize
           -> DFA a -- DFA realized
minimalDFA a (DFA su si sf t) =
    let partition = (S.fromList [si, sf])
        worklist = S.singleton sf
        hfinal = runEndo (H partition worklist su a t) $ refineStep
        su' = hp hfinal
        -- | should contain all initial states: NOTE: is this correct?
        si'= S.filter (si `S.isSubsetOf`) $ su'
        -- | should contain some final state
        sf' = S.filter (`S.isSubsetOf` sf) $ su'
        -- | To transition, find the equivalence class of the transitioned set
        t' a ss = S.map (t a) ss
     in DFA su' si' sf' t'


-- | Dot product of numbers with bit-vector
bvdot :: [Int] -> BV -> Int
bvdot xs bv =
  sum $ zipWith (\x ix -> if (bv .!. ix) then x else 0)
                xs [0..(length xs - 1)]


dfaPrNTransition ::
  ([Int], Int) -- as, b
  -> BV -- ^ input bitvector
  -> Int -- ^ state of the DFA
  -> Int -- ^ output state of the DFA
dfaPrNTransition (as, b) zeta q = (q - bvdot as zeta) // 2


-- | Create the transitive closure of the transition relation starting from
-- the initial state "b" for the DFA for `a. x <= b`. See also @dfaPrN
dfaPrNUniv ::
  ([Int], Int) -- ^ tuple contains (a, b) for (a . x <= b)
  -> S.Set Int
dfaPrNUniv (as, b) =
    let
      -- | alphabet to consider
      zetas = bvPowerSet $ S.fromList $ [0..(length as - 1)]
      -- | Transition given alphabet and state
      t = dfaPrNTransition (as, b)
      -- | Fix set
      fixSet f s = let s' = f s in if s' == s then s' else fixSet f s'
    in
      fixSet (\univ -> univ `S.union` (S.map (uncurry t) (zetas `S.cartesianProduct` univ))) $
        S.singleton b



-- | create a finite automata for a . x <= b, where a ∈ Z^n, p ∈ Z, x ∈ N^n
dfaPrN ::
  ([Int], Int) -- ^ (Vector of a: [a !! i == coeff of BV .!. i], b) such that (a.x <= b)
  -> DFA BV
dfaPrN (as, b) =
    let su = dfaPrNUniv (as, b)
        si = S.singleton b -- ^ the initial state starts with our value
        sf = S.filter (>= 0) su -- ^ all states that are >= 0 are final states since they accept the empty word
        t = dfaPrNTransition (as, b)
    in DFA su si sf t


newtype ListMaxSized (smax :: Nat) (a :: *) =
  ListMaxSized [a] deriving(Eq, Show, Ord)


instance (Arbitrary a, KnownNat smax) => Arbitrary (ListMaxSized smax a) where
  arbitrary = do
    n <- choose (1, natVal (Proxy :: Proxy smax))
    xs <- vectorOf (fromInteger n) arbitrary
    return $ ListMaxSized xs

-- quickCheck property for presburget set on Ns
qcDFAPrN :: ListMaxSized 5 (Int, NonNegative Int) -> Int -> Bool
qcDFAPrN (ListMaxSized asAndXs) p =
    let as = map fst asAndXs
        xs = map (getNonNegative . snd) asAndXs
        out = sum (zipWith (*) as xs) <= p
        dfa = dfaPrN (as, p)
        input = mkInputBitsN xs
     in runDFA dfa input == out


-- | forall x. forall y. eq x y
-- acceptsEmpty eg1 =  False
eg1 :: NFA BV
eg1 = forall 1 $ forall  0 $ eq 0 1



-- | Same as eg1, but with minmize in between
eg1' :: NFA BV
eg1' =
    let shrink = nfaRemoveUnreachableAfterN 64 (bvPowerSet $ S.fromList $ [0..1])
     in shrink $ forall 1 $ shrink $ forall 0 $ eq 0 1

-- | Same as eg1, but with minimal DFA
eg1'' :: DFA BV
eg1'' =
    let shrink = nfaRemoveUnreachableAfterN 64 (bvPowerSet $ S.fromList $ [0..1])
        minimize = nfa2dfaMinimalAfterN 64 (bvPowerSet $ S.fromList $ [0..1])
     in minimize $ forall 1 $ shrink $ forall 0 $ eq 0 1



-- | forall x. exists y. eq x y
-- acceptsEmpty eg2 = true
eg2 :: NFA BV
eg2 = forall 1 $ exists  0 $ eq 0 1


-- | exists x. forall y. eq x y
-- acceptsEmpty eg2 = false
eg3 :: NFA BV
eg3 = exists 1 $ forall  0 $ eq 0 1


-- | 2x - y <= 2
eg4 :: DFA BV
eg4 = dfaPrN ([2, 3], 2)


-- | -x <= -2
eg5 :: DFA BV
eg5 = dfaPrN ([-1], -2)


-- | -7x <= -3
eg6 :: DFA BV
eg6 = dfaPrN ([-7], -3)

-- | -x <= 0
eg7 :: NFA BV
eg7 = nfaPrZ ([-1], 0)


-- | -3x <= 0
eg8 :: NFA BV
eg8 = nfaPrZ ([-3], 0)


assert_ :: Bool -> String -> IO ()
assert_ True _ = pure ()
assert_ False s = error $ "failed check: " <> s


-- | Number of bits needed to represent a number in 2s complement
nbits2scomplement :: Int -> Int
nbits2scomplement x =
    let lb2 a = logBase 2 (fromIntegral (abs a))
     in if x == 0
        then 1
        else if x >= 0
        then 1 + ceiling (lb2 (x + 1))
        else 1 + floor (lb2 x)


-- | Number of bits if interpreted a N number in base 2
nbitsN :: Int -> Int
nbitsN x =
  if x < 0
  then error $ show x <> " : cannot be negative as param to nbitsN"
  else if x <= 1
  then 1
  else 1 + nbitsN (x // 2)

-- | Convert a list of N number to input that can
-- be fed into the Pr engine as a list of bitvectors.
-- *Main> mkInputBitsN [1, 3] -> [BV 3,BV 2]
-- *Main> mkInputBitsN [1, 2] -> [BV 1,BV 2]
-- *Main> mkInputBitsN [2, 2] -> [BV 0,BV 3]
mkInputBitsN :: [Int] -> [BV]
mkInputBitsN xs =
  let maxnbits = foldl1 max (map nbitsN xs) in
  map (\i -> toBV $ map (`testBit` i) xs) [0..(maxnbits - 1)]


-- | Convert a list of integerss to 2s complement
-- input that can be fed into the Presburger
-- engine as a list of bitvectrs.
-- *Main> mkInputBitsZ [-3]: [BV 1,BV 1]
-- *Main> mkInputBitsZ [-1]: [BV 1]
-- *Main> mkInputBitsZ [2]: [BV 0,BV 0,BV 1]
-- *Main> mkInputBitsZ [1]: [BV 0,BV 1]
mkInputBitsZ :: [Int] -> [BV]
mkInputBitsZ xs =
  let maxnbits = foldl1 max (map nbits2scomplement xs)
      xs' = map (\x -> if x >= 0 then x else (-2 * x + 1)) xs
      sliceBits ix = toBV $ map (`testBit` ix) xs'
 in map sliceBits [0..(maxnbits - 1)]



-- | States in the Presburger Z automata.
-- We need to add a dedicated final state
data PresState = PSInt Int | PSFinal deriving(Eq, Show, Ord)


-- | Transition relation for NFA
nfaPrZTransition ::
  ([Int], Int)
  -> BV
  -> PresState
  -> S.Set PresState
nfaPrZTransition _ _ PSFinal = S.empty
nfaPrZTransition (as, b) zeta (PSInt q) =
  let j = (q - bvdot as zeta) // 2
      j' = q + bvdot as zeta
      qf = if j' >= 0 then [PSFinal] else []
   in S.fromList $ qf ++ [PSInt j]

-- | Create the transitive closure of the transition relation starting from
-- the initial state "b" for the DFA for `a. x <= b`. See also @dfaPrN
nfaPrZUniv ::
  ([Int], Int) -- ^ tuple contains (a, b) for (a . x <= b)
  -> S.Set PresState
nfaPrZUniv (as, b) =
    let
      -- | alphabet to consider (this is slightly wrong)
      zetas = bvPowerSet $ S.fromList $ [0..(length as - 1)]
      -- | Fix set
      fixSet f s = let s' = f s in if s == s' then s' else fixSet f s'
      t = nfaPrZTransition (as, b)
    in
      fixSet (\univ -> univ `S.union`
      (foldMap (\q ->
          foldMap (\zeta -> t zeta q) zetas) univ)) $ S.singleton $ PSInt b


-- | NFA, can solve a . x <= b for a, x ∈ Z^n, b ∈ Z
nfaPrZ :: ([Int], Int) -- as, b
  -> NFA BV
nfaPrZ (as, b) =
    let su = nfaPrZUniv (as, b)
        t = nfaPrZTransition (as, b)
        sf = S.singleton PSFinal
        si = S.singleton (PSInt b)
     in NFA su si sf t

-- quickCheck property for presburget set on Zs
qcNFAPrZ :: ListMaxSized 5 (Int, Int) -> Int -> Bool
qcNFAPrZ (ListMaxSized asAndXs) p =
    let as = map fst asAndXs
        xs = map (abs . snd) asAndXs
        out = sum (zipWith (*) as xs) <= p
        nfa = nfaPrZ (as, p)
        input = mkInputBitsZ xs
     in runNFA nfa input == out

main :: IO ()
main = do
    assert_ (nfaAcceptsEmpty eg1 == False) "eg1"
    assert_ (nfaAcceptsEmpty eg1' == False) "eg1'"
    assert_ (dfaAcceptsEmpty eg1'' == False) "eg1''"
    assert_ (nfaAcceptsEmpty eg2 == True) "eg2"
    assert_ (nfaAcceptsEmpty eg3 == False) "eg3"
    -- 2x + 3y <= 2
    assert_ (runDFA eg4 [BV 0] == True) "eg4 - 0"
    assert_ (runDFA eg4 [BV 1] == True) "eg4 - 1"
    assert_ (runDFA eg4 [BV 2] == False) "eg4 - 2"
    assert_ (runDFA eg4 [BV 3] == False) "eg4 - 3"
    assert_ (runDFA eg5 (mkInputBitsN [2]) == True) "eg5"
    assert_ (runDFA eg6 (mkInputBitsN [4]) == True) "eg6"
    assert_ (runNFA eg7 (mkInputBitsZ [1]) == True) "eg7"
    assert_ (runNFA eg8 (mkInputBitsZ [0]) == True) "eg8"

    quickCheck $ counterexample "qcToBV" qcToBV
    quickCheck $ counterexample "qcDFA" qcDFAPrN
    quickCheck $ counterexample "qcNFA" qcNFAPrZ

    putStrLn $ "Pr"
