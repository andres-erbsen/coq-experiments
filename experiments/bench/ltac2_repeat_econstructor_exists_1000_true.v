Require Import Ltac2.Ltac2.
Import Ltac2.Control.

Fixpoint fex (n : nat) : Prop :=
  match n with
  | O => True
  | S n => exists x : True, fex n
  end.

Goal fex 1000. Time repeat econstructor. Time Qed.
(*
Finished transaction in 1.104 secs (1.089u,0.009s) (successful)
Finished transaction in 2.106 secs (2.096u,0.s) (successful)
*)
