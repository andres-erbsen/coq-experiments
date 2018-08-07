Require Import Coq.Init.Prelude.

Fixpoint fex (n : nat) : Prop :=
  match n with
  | O => True
  | S n => exists x : True, fex n
  end.

Goal fex 1000. Time repeat econstructor. Time Qed.
(*
Finished transaction in 1.171 secs (1.162u,0.003s) (successful)
Finished transaction in 2.044 secs (2.035u,0.s) (successful)
*)
