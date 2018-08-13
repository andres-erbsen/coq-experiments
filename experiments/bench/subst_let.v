Require Import Coq.Init.Prelude.

Fixpoint letn n (x : nat) (k : nat -> Prop) :=
  match n with
  | O => k x
  | S n =>
    let x := S x in
    letn n x k
  end.

Ltac substs := repeat lazymatch goal with x := _ |- _ => subst x end.

(*
Goal letn 250 O (fun _ => True). cbv beta iota delta [letn]. intros. Optimize Proof. Time substs. exact I. Qed.
Goal letn 500 O (fun _ => True). cbv beta iota delta [letn]. intros. Optimize Proof. Time substs. exact I. Qed.
Goal letn 1000 O (fun _ => True). cbv beta iota delta [letn]. intros. Optimize Proof. Time substs. exact I. Qed.
Goal letn 2000 O (fun _ => True). cbv beta iota delta [letn]. intros. Optimize Proof. Time substs. exact I. Qed.
Goal letn 4000 O (fun _ => True). cbv beta iota delta [letn]. intros. Optimize Proof. Time substs. exact I. Qed.
(* Evars: 253 -> 1 Finished transaction in 0.015 secs (0.015u,0.s) (successful) *)
(* Evars: 503 -> 1 Finished transaction in 0.123 secs (0.119u,0.003s) (successful) *)
(* Evars: 1003 -> 1 Finished transaction in 0.398 secs (0.381u,0.016s) (successful) *)
(* Evars: 2003 -> 1 Finished transaction in 1.302 secs (1.275u,0.023s) (successful) *)
(* Evars: 4003 -> 1 Finished transaction in 6.674 secs (6.552u,0.099s) (successful) *)
*)

Goal letn 250 O (fun _ => True). cbv beta iota delta [letn]. intros. Optimize Proof. substs. Time Optimize Proof. exact I. Qed.
Goal letn 500 O (fun _ => True). cbv beta iota delta [letn]. intros. Optimize Proof. substs. Time Optimize Proof. exact I. Qed.
Goal letn 1000 O (fun _ => True). cbv beta iota delta [letn]. intros. Optimize Proof. substs. Time Optimize Proof. exact I. Qed.
Goal letn 2000 O (fun _ => True). cbv beta iota delta [letn]. intros. Optimize Proof. substs. Time Optimize Proof. exact I. Qed.
Goal letn 4000 O (fun _ => True). cbv beta iota delta [letn]. intros. Optimize Proof. substs. Time Optimize Proof. exact I. Qed.
(* Evars: 253 -> 1 Evars: 501 -> 1 Finished transaction in 0.032 secs (0.028u,0.003s) (successful) *)
(* Evars: 503 -> 1 Evars: 1001 -> 1 Finished transaction in 0.173 secs (0.172u,0.s) (successful) *)
(* Evars: 1003 -> 1 Evars: 2001 -> 1 Finished transaction in 1.465 secs (1.464u,0.s) (successful) *)
(* Evars: 2003 -> 1 Evars: 4001 -> 1 Finished transaction in 13.74 secs (13.714u,0.013s) (successful) *)
(* Evars: 4003 -> 1 Evars: 8001 -> 1 Finished transaction in 149.144 secs (148.217u,0.265s) (successful) *)
