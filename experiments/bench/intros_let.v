Require Import Coq.Init.Prelude.

Fixpoint letn n (x : nat) (k : nat -> Prop) :=
  match n with
  | O => k x
  | S n =>
    let x := S x in
    letn n x k
  end.

Goal letn 250 O (fun _ => True). cbv beta iota delta [letn]. Time intros. Time Optimize Proof. exact I. Qed.
(*Finished transaction in 0.029 secs (0.022u,0.006s) (successful)
Evars: 253 -> 1
Finished transaction in 0.012 secs (0.012u,0.s) (successful) *)
Goal letn 500 O (fun _ => True). cbv beta iota delta [letn]. Time intros. Time Optimize Proof. exact I. Qed.
(* Finished transaction in 0.055 secs (0.054u,0.s) (successful)
Evars: 503 -> 1
Finished transaction in 0.123 secs (0.122u,0.s) (successful) *)
Goal letn 1000 O (fun _ => True). cbv beta iota delta [letn]. Time intros. Time Optimize Proof. exact I. Qed.
(* Finished transaction in 0.264 secs (0.257u,0.006s) (successful)
Evars: 1003 -> 1
Finished transaction in 0.73 secs (0.726u,0.003s) (successful) *)
Goal letn 2000 O (fun _ => True). cbv beta iota delta [letn]. Time intros. Time Optimize Proof. exact I. Qed.
(* Finished transaction in 1.09 secs (1.077u,0.009s) (successful)
Evars: 2003 -> 1
Finished transaction in 6.754 secs (6.741u,0.006s) (successful) *)
Goal letn 4000 O (fun _ => True). cbv beta iota delta [letn]. Time intros. Time Optimize Proof. exact I. Qed.
(* Finished transaction in 4.324 secs (4.235u,0.079s) (successful)
Evars: 4003 -> 1
Finished transaction in 68.641 secs (68.531u,0.073s) (successful) *)

(* Optimize Proof: time ~=~ n^3 * 1e-9 *)