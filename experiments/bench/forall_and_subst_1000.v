Require Import Coq.Init.Prelude.

Fixpoint frn (n : nat) (acc : Prop) : Prop :=
  match n with
  | 0 => acc
  | S n => True /\ forall x : nat, frn n (x = x /\ acc)
  end.

Goal frn 1000 True. Time repeat constructor. Time Qed.
(*
Finished transaction in 9.252 secs (8.916u,0.289s) (successful)
Finished transaction in 11.262 secs (11.15u,0.069s) (successful)
*)