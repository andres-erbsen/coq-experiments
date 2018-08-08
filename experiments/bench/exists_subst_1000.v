Require Import Coq.Init.Prelude.

Fixpoint frn (n : nat) (acc : Prop) : Prop :=
  match n with
  | 0 => acc
  | S n => exists x : unit, frn n (x = x /\ acc)
  end.

Goal frn 1000 True. Time repeat unshelve econstructor. Time Qed.
(*
Finished transaction in 8.284 secs (8.037u,0.208s) (successful)
Finished transaction in 12.213 secs (12.114u,0.036s) (successful)
*)