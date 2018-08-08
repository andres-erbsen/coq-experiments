Require Import Coq.Init.Prelude.

Fixpoint frn (n : nat) (acc : Prop) : Prop :=
  match n with
  | 0 => acc
  | S n => forall x : nat, frn n (x = x /\ acc)
  end.

Goal frn 1000 True. Time repeat constructor. Time Qed.
(*
Finished transaction in 17.331 secs (4.705u,1.833s) (successful)
Finished transaction in 3.095 secs (3.082u,0.s) (successful)
*)