Require Import Coq.Init.Prelude.

Fixpoint foralln n (x : nat) (k : nat -> Prop) :=
  match n with
  | O => k x
  | S n =>
    forall x : nat, foralln n x k
  end.

Goal foralln 250 O (fun _=> True). cbv beta iota delta [foralln]. Time intros. Time Optimize Proof. exact I. Qed.
(* Finished transaction in 0.034 secs (0.034u,0.s) (successful)
Evars: 253 -> 1
Finished transaction in 0.012 secs (0.011u,0.s) (successful) *)
Goal foralln 500 O (fun _=> True). cbv beta iota delta [foralln]. Time intros. Time Optimize Proof. exact I. Qed.
(* Finished transaction in 0.052 secs (0.051u,0.s) (successful)
Evars: 503 -> 1
Finished transaction in 0.113 secs (0.113u,0.s) (successful) *)
Goal foralln 1000 O (fun _=>True). cbv beta iota delta [foralln]. Time intros. Time Optimize Proof. exact I. Qed.
(* Finished transaction in 0.217 secs (0.213u,0.003s) (successful)
Evars: 1003 -> 1
Finished transaction in 0.796 secs (0.795u,0.s) (successful) *)
Goal foralln 2000 O (fun _=>True). cbv beta iota delta [foralln]. Time intros. Time Optimize Proof. exact I. Qed.
(* Finished transaction in 0.944 secs (0.924u,0.016s) (successful)
Evars: 2003 -> 1
Finished transaction in 6.819 secs (6.801u,0.009s) (successful) *)
Goal foralln 4000 O (fun _=>True). cbv beta iota delta [foralln]. Time intros. Time Optimize Proof. exact I. Qed.
(* Finished transaction in 4.415 secs (4.384u,0.016s) (successful)
Evars: 4003 -> 1
Finished transaction in 72.025 secs (71.63u,0.122s) (successful) *)