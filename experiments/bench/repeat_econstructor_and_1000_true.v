Require Import Coq.Init.Prelude.

Fixpoint fnd (n : nat) : Prop :=
  match n with
  | O => True
  | S n => True /\ fnd n
  end.

Goal fnd 1000. Time repeat econstructor. Time Qed.
(*
Finished transaction in 1.187 secs (1.128u,0.051s) (successful)
Finished transaction in 1.671 secs (1.659u,0.003s) (successful)
*)
