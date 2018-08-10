Require Import Coq.Init.Prelude.

Fixpoint deep (n : nat) : Set :=
  match n with
  | O => unit
  | S n => option (deep n)
  end.

Goal deep 1000.
  Time assert (deep 1000) by (abstract (repeat constructor)).
  assumption.
Time Qed.
(*
Finished transaction in 2.879 secs (2.764u,0.099s) (successful)
Finished transaction in 0.654 secs (0.651u,0.s) (successful)
*)

Goal deep 1000.
  Time assert (deep 1000) by (repeat constructor).
  assumption.
Time Qed.
(*
Finished transaction in 1.238 secs (1.213u,0.016s) (successful)
Finished transaction in 1.63 secs (1.62u,0.s) (successful)
*)
