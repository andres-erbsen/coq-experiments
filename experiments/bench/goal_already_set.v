Require Import Coq.Init.Prelude.

Inductive good : nat -> Prop :=
| good_O : good O
| good_S n (_:good n) : good (S n).

Fixpoint letn n (x : nat) (k : nat -> Prop) :=
  match n with
  | O => k x
  | S n =>
    let x := S x in
    letn n x k
  end.

Ltac prepare :=
  lazymatch goal with
  | |- ?P ?n =>
      let G := eval cbv beta iota delta [letn] in (let x := 0 in letn n x P) in
      change G
  end; intros.

Ltac construct :=
  repeat lazymatch goal with
  | |- good ?x =>
    let x := eval unfold x in x in
    lazymatch x with
    | S ?y => refine (good_S y _)
    | O => refine good_O
    end
  end.

Goal good 125. prepare. Optimize Proof. Time construct. Abort.
Goal good 250. prepare. Optimize Proof. Time construct. Abort.
Goal good 500. prepare. Optimize Proof. Time construct. Abort.
Goal good 1000. prepare. Optimize Proof. Time construct. Abort.
Goal good 2000. prepare. Optimize Proof. Time construct. Abort.
(* Evars: 128 -> 1
Evars: 253 -> 1
Finished transaction in 0.072 secs (0.072u,0.s) (successful)
Evars: 503 -> 1
Finished transaction in 0.408 secs (0.407u,0.s) (successful)
Evars: 1003 -> 1
Finished transaction in 1.8 secs (1.783u,0.009s) (successful)
Evars: 2003 -> 1
Finished transaction in 8.208 secs (7.924u,0.249s) (successful)
*)

(*
Goal good 125. prepare. Optimize Proof. Time construct. Time Optimize Proof. Time Qed.
Goal good 250. prepare. Optimize Proof. Time construct. Time Optimize Proof. Time Qed.
Goal good 500. prepare. Optimize Proof. Time construct. Time Optimize Proof. Time Qed.
Goal good 1000. prepare. Optimize Proof. Time construct. Time Optimize Proof. Time Qed.
Goal good 2000. prepare. Optimize Proof. Time construct. Time Optimize Proof. Time Qed.
*)