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

Goal fnd 10000.
  Time
  let n := match goal with |- fnd ?n => n end in
  let ls := eval cbv in (repeat True n) in
  let pf := constr:(big_conj ls) in
  let T := type of pf in
  let T := eval cbv [typeof_big_conj big_and] in T in
  refine (let H : T := pf in _).
  Time clearbody H.
  Time apply H; exact I.
Time Qed.
(*
Finished transaction in 3.028 secs (2.946u,0.067s) (successful)
Finished transaction in 0.001 secs (0.001u,0.s) (successful)
Finished transaction in 21.168 secs (21.078u,0.017s) (successful)
Finished transaction in 3.405 secs (3.397u,0.s) (successful)
*)
