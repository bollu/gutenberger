{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
import qualified Data.Set as S
import Data.Bits

data NFA a where
    NFA :: Ord s => S.Set s -- ^ universe: su
      -> (S.Set s) -- ^ initial: si
      -> (S.Set s) -- ^ final: sf
      -> (a -> s -> S.Set s) -- ^ transition: t
      -> NFA a

-- | NFA that accepts all states
univ :: NFA a
univ = let su = S.singleton () in NFA su su su (\ _ _ -> su)

-- | NFA that accepts no state
empty :: NFA a
empty = let su = S.singleton () in NFA su su S.empty (\ _ _ -> su)



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

-- | Accepts complement of two languages
nfaComplement :: NFA a -> NFA a
nfaComplement (NFA su si sf t) = NFA  su si (su S.\\ sf) t

-- | Perform a non-deterministic step of the NFA
nondet :: Ord s => (a -> s -> S.Set s) -> a -> S.Set s -> S.Set s
nondet f a s = foldMap (f a) s



-- | Run multiple steps of the NFA
nondets :: Ord s => Foldable g  => (a -> s -> S.Set s) -> g a -> S.Set s -> S.Set s
nondets f aa ss = foldr (nondet f) ss aa

-- | Check if two sets have non-empty intersection
intersects :: Ord s => S.Set s -> S.Set s -> Bool
intersects xs ys = not $ S.null $ S.intersection xs ys

-- | Return set of values reachable (this includes interior nodes)
-- from transition relation and initial state
-- given input stream
visited :: (Foldable f, Ord s) => (a -> s -> S.Set s) -> f a -> S.Set s -> S.Set s
visited d aa = fixSet $ \s -> (nondets d aa s) `S.union` s where
  fixSet f a
    | a == a'   = a
    | otherwise = fixSet f a'
    where a' = f a
{-# inline visited #-}

-- | Check whether NFA accepts
runNFA :: NFA a -> [a] -> Bool
runNFA (NFA _ si sf t) aa = intersects (nondets t aa si) sf

-- | Now encode PA as NFAs

-- | Key for the variable: ith variable is natural number i.
type Var = Int

-- | Bitvector.
newtype BV = BV Int deriving(Eq, Ord, Show, Bits)

(.!.) :: BV -> Int -> Bool
(.!.) (BV bv) ix = testBit bv ix

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

-- | Create a list containing bit vectors that have the
-- given var bit both on and off
enableDisableBit :: BV ->  Var -> [BV]
enableDisableBit v i = [setBit v i, clearBit v i]

-- | Create an NFA for:  exists x. P x
-- find all states reachable from the state where i is enabled
-- (and also from 0, why??)
exists :: Var -> NFA BV -> NFA BV
exists i (NFA su si sf t) =
  let si' = visited t (BV 0 `enableDisableBit` i) si
      t' v s =
          foldMap (\curv -> t curv s)
                  (v `enableDisableBit` i)
  in NFA su si' sf t'

-- | Create an NFA for: forall x. P x
-- Encode this as not (exists x. not (P x))
forall :: Var -> NFA BV -> NFA BV
forall i = nfaComplement . exists i . nfaComplement


main :: IO ()
main = putStrLn $ "presburger"
