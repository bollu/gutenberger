Require Import ZArith.
Require Import ListSet.

(** States in the NFA **)
Inductive St := StZ : Z -> St  | StF : St.

(** bit vector **)
Inductive BV := mkBV : list bool -> BV.



(** Presburger machine **)
Inductive P :=
  mkP : set St (* Init state *)
        -> set St (* final state *)
        -> (St -> BV -> set St) (* transition *)
        -> P.


(** Non deterministic step **)
Definition nondet
           (t: St -> BV -> set St)
           (sts: set St)
           (bv: BV) : set St.
Admitted.
