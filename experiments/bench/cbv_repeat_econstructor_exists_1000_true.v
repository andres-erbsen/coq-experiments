Require Import Coq.Init.Prelude.

Fixpoint fex (n : nat) : Prop :=
  match n with
  | O => True
  | S n => exists x : True, fex n
  end.

Goal fex 1000. Time cbv. Time repeat econstructor. Time Qed.
(*
Finished transaction in 0.033 secs (0.03u,0.003s) (successful)
Finished transaction in 2.129 secs (2.098u,0.022s) (successful)
Finished transaction in 2.596 secs (2.584u,0.003s) (successful)
*)