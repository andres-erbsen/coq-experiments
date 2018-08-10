Require Import Coq.Init.Prelude.

Inductive prop :=
| Nil
| And (_:Prop) (_ : prop)
| Exis {T : Type} (_ : T -> prop).

Fixpoint interp_prop (p : prop) :=
  match p with
  | Nil => True
  | And A p => A /\ interp_prop p
  | Exis f => exists x, interp_prop (f x)
  end.

Fixpoint uncurry_prop (p : prop) (Q : Prop) :=
  match p with
  | Nil => Q
  | And A p => A -> uncurry_prop p Q
  | Exis f => forall x, uncurry_prop (f x) Q
  end.

Lemma uncurry_prop_and_r xs (P Q : Prop) : P -> uncurry_prop xs Q -> uncurry_prop xs (P /\ Q).
Proof. revert Q; revert P; induction xs; intros; cbn in *; eauto. Qed.
Lemma uncurry_prop_exists_r xs {T : Type} (P : T -> Prop) (x : T) : uncurry_prop xs (P x) -> uncurry_prop xs (exists x, P x).
Proof. revert dependent P; induction xs; intros; cbn in *; eauto. Qed.
Lemma uncurry_interp_prop p : uncurry_prop p (interp_prop p).
Proof. induction p; cbn in *; intros; eauto using uncurry_prop_and_r, uncurry_prop_exists_r. Qed.

Fixpoint Fex (t_prev : unit) (n : nat) : prop :=
  match n with
  | O => Nil
  | S n => Exis (fun t:unit => And (t = t_prev) (Fex t n))
  end.

Fixpoint fex (t_prev : unit) (n : nat) : Prop :=
  match n with
  | O => True
  | S n => exists t:unit, t = t_prev /\ fex t n
  end.

Goal fex tt 10000.
  Time (
    let n := match goal with [ |- fex tt ?n ] => n end in
    let p := constr:(Fex tt n) in
    let p := (eval cbv in p) in
    let pf := constr:(uncurry_interp_prop p) in
    let t := type of pf in
    let t := (eval cbv [uncurry_prop interp_prop] in t) in
    refine (let H : t := pf in _ )).
  Time clearbody H.
  Time eapply H.
  Time all: exact eq_refl.
Time Qed.
(*
Finished transaction in 5.965 secs (5.375u,0.57s) (successful)
Finished transaction in 0.001 secs (0.u,0.s) (successful)
Finished transaction in 87.529 secs (87.247u,0.006s) (successful)
Finished transaction in 89.998 secs (89.667u,0.073s) (successful)
Finished transaction in 42.641 secs (42.496u,0.006s) (successful)
*)
