Require Import Coq.Init.Prelude.
Require Import Coq.Setoids.Setoid.

Axiom incr_Some : option nat -> option nat.
Axiom eqn : forall n, incr_Some (Some n) = Some (S n).

Fixpoint pln (n : nat) : option nat :=
  match n with
  | O => Some O
  | S n => incr_Some (pln n)
  end.

Goal pln 1000 = Some 1000.
  Time cbv [pln]. Fail Timeout 60 (rewrite_strat (bottomup (eqn))). Abort.