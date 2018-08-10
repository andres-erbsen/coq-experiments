Require Import Coq.Init.Prelude.

Module Import flat.
  Inductive prop :=
  | Trivial
  | Atom (_ : Prop)
  | And (_:Prop) (_ : prop)
  | Exis {T : Type} (_ : T -> prop).
  
  Fixpoint interp_prop (p : prop) :=
    match p with
    | Trivial => True
    | Atom P => P
    | And A p => A /\ interp_prop p
    | Exis f => exists x, interp_prop (f x)
    end.
  
  Fixpoint uncurry (p : prop) (Q : Prop) : Prop :=
    match p with
    | Trivial => Q
    | Atom P => P -> Q
    | And A p => A -> uncurry p Q
    | Exis f => forall x, uncurry (f x) Q
    end.
  
  Lemma interp_prop_uncurry p (Q : Prop) : (interp_prop p -> Q) <-> uncurry p Q.
  Proof. revert Q. induction p; cbn in *; solve [firstorder]. Qed.

  Lemma uncurry_impl_r xs (P Q : Prop) : (P -> Q) -> uncurry xs P -> uncurry xs Q.
  Proof. revert Q; revert P; induction xs; intros; cbn in *; firstorder eauto. Qed.
  Lemma uncurry_and_r xs (P Q : Prop) : P -> uncurry xs Q -> uncurry xs (P /\ Q).
  Proof. revert Q; revert P; induction xs; intros; cbn in *; firstorder eauto. Qed.
  Lemma uncurry_exists_r xs {T : Type} (P : T -> Prop) (x : T) : uncurry xs (P x) -> uncurry xs (exists x, P x).
  Proof. revert dependent P; induction xs; intros; cbn in *; firstorder eauto. Qed.

  Lemma uncurry_interp_prop p : uncurry p (interp_prop p).
  Proof. apply interp_prop_uncurry. trivial. Qed.

  Definition and (P : Prop) (q : prop) : prop :=
    match q with
    | Trivial => Atom P
    | _ => And P q
    end.
  Lemma and_sound (P : Prop) (q : prop) : interp_prop (and P q) -> P /\ interp_prop q.
  Proof. destruct q; firstorder idtac. Qed.
End flat.

Inductive prop :=
| Atom (_ : Prop)
| And (_ _:prop)
| Exis {T : Type} (_ : T -> prop).

Fixpoint interp_prop (p : prop) : Prop :=
  match p with
  | Atom P => P
  | And A B => Logic.and (interp_prop A) (interp_prop B)
  | Exis P => exists x, (interp_prop (P x))
  end.

Fixpoint flatten (p : prop) (k : flat.prop) : flat.prop :=
  match p with
  | Atom P => flat.and P k
  | And A B => flatten A (flatten B k)
  | @Exis T p => @flat.Exis T (fun x => flatten (p x) k)
  end.
Compute flatten (Exis (fun tt => And (Atom True) (Atom False))) (flat.Trivial).

Lemma flatten_sound p k : flat.interp_prop (flatten p k) -> flat.interp_prop k /\ interp_prop p.
Proof.
  pose proof flat.and_sound.
  revert k; induction p; cbn in *; solve [firstorder idtac].
Qed.

Lemma flatten_sound_Trivial p : flat.interp_prop (flatten p flat.Trivial) -> interp_prop p.
Proof. apply flatten_sound. Qed.

Lemma uncurry_sound p : uncurry (flatten p Trivial) (interp_prop p).
Proof. eauto using uncurry_impl_r, uncurry_interp_prop, flatten_sound_Trivial. Qed.


Fixpoint big (n : nat) (y : unit) : prop :=
  match n with
  | O => Atom (y = tt)
  | S n => Exis (fun x : unit => And (big n x) (big n x))
  end.
