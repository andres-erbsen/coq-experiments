Require Import Coq.Init.Datatypes Coq.Init.Nat Coq.Init.Prelude.
Fixpoint fin (n : Datatypes.nat) : Type :=
  match n with
  | O => unit
  | S n => option (fin n)
  end.

Goal fin 1000. Time repeat econstructor. Time Qed.
(*
Finished transaction in 1.165 secs (1.14u,0.019s) (successful)
Finished transaction in 1.563 secs (1.554u,0.003s) (successful)
*)
