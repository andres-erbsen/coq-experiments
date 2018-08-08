Require Import Coq.Init.Prelude.

Fixpoint frn (n : nat) (acc : Prop) : Prop :=
  match n with
  | 0 => acc
  | S n => True /\ exists x : unit, frn n (x = x /\ acc)
  end.

Goal frn 1000 True. Time repeat unshelve econstructor. Time Qed.
(*
Finished transaction in 12.723 secs (12.42u,0.235s) (successful)
Finished transaction in 19.923 secs (19.502u,0.112s) (successful)
*)