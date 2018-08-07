Require Import Coq.Init.Datatypes Coq.Init.Nat Coq.Init.Prelude.
Fixpoint fin (n : Datatypes.nat) : Type :=
  match n with
  | O => unit
  | S n => option (fin n)
  end.

Goal fin 1000. cbv. Time repeat econstructor. Time Qed.
(*
Finished transaction in 1.701 secs (1.588u,0.106s) (successful)
Finished transaction in 1.093 secs (1.09u,0.s) (successful)
*)