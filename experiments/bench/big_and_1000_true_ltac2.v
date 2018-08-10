Require Import Coq.Init.Prelude.

Fixpoint fnd (n : nat) : Prop :=
  match n with
  | O => True
  | S n => True /\ fnd n
  end.

Fixpoint big_and (xs : list Prop) : Prop :=
  match xs with
  | nil => True
  | cons x xs => and x (big_and xs)
  end.
Fixpoint typeof_big_conj (xs : list Prop) (P : Prop) : Prop :=
  match xs with
  | nil => P
  | cons x xs => x -> typeof_big_conj xs P
  end.
Lemma apply_rconj_and xs (P Q : Prop) : P -> typeof_big_conj xs Q -> typeof_big_conj xs (P /\ Q).
Proof. revert Q; revert P; induction xs; intros; cbn in *; eauto. Qed.
Lemma big_conj xs : typeof_big_conj xs (big_and xs).
Proof. induction xs. exact I. cbn. intros. apply apply_rconj_and; eauto. Qed.

Require Import Coq.Lists.List.

Require Import Ltac2.Ltac2.
Require Import Ltac2.Control.
Require Import Ltac2.Std.
Require Import Ltac2.Notations.

Ltac2 get_constant (c : constr)
  := match Constr.Unsafe.kind c with
     | Constr.Unsafe.Constant c _ => c
     | _ => throw Match_failure
     end.

Ltac2 Notation "eval" "cbv" s(strategy) "in" v(constr) :=
  Std.eval_cbv s v.

Goal fnd 1000.
  Time
    let n := match! goal with [ |- fnd ?n ] => n end in
    let ls := constr:(repeat True $n) in
    let ls := (eval cbv in $ls) in
    let pf := constr:(big_conj $ls) in
    let t := Constr.type pf in
    let t := (eval cbv [typeof_big_conj big_and] in $t) in
    (assert (H : $t) by refine pf); apply H; exact I.
Time Qed.
(*
Finished transaction in 0.281 secs (0.23u,0.049s) (successful)
Finished transaction in 0.044 secs (0.044u,0.s) (successful)
*)
