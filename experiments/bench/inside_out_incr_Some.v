Require Import Coq.Init.Prelude.

Axiom incr_Some : option nat -> option nat.
Axiom eqn : forall n, incr_Some (Some n) = Some (S n).

Fixpoint pln (n : nat) : option nat :=
  match n with
  | O => Some O
  | S n => incr_Some (pln n)
  end.

Goal pln 1000 = Some 1000.
  Time cbv [pln]. Time repeat rewrite eqn. Time reflexivity. Time Qed.
(*
Finished transaction in 0. secs (0.u,0.s) (successful)
Finished transaction in 21.264 secs (21.133u,0.049s) (successful)
Finished transaction in 0.003 secs (0.003u,0.s) (successful)
Finished transaction in 6.073 secs (6.047u,0.006s) (successful)
*)