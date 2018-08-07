Declare ML Module "ltac_plugin".
Local Set Default Proof Mode "Classic".
(* *)
Set Universe Polymorphism.
Unset Universe Minimization ToSet.
(* *)
Set Primitive Projections.
Unset Printing Primitive Projection Parameters.
Set Printing Projections.
Set Case Analysis Schemes.
Set Nonrecursive Elimination Schemes.
(* *)
Delimit Scope type_scope with type.
Delimit Scope function_scope with function.
Delimit Scope core_scope with core.
Bind Scope type_scope with Sortclass.
Bind Scope function_scope with Funclass.
Open Scope core_scope.
Open Scope function_scope.
Open Scope type_scope.

(** Inhabiting inductive families using only ∀ ∃ 0 1 ℕ *)

(** N-types are a TODO work-in-progress alternative to W-types, aiming to improve on both intensional properties and simplicity *)
(* Leave my types ∀10ℕ∃! *)
(* fueled types *)

(** ∀ is built-in in Coq *)
Record exi {A B} := pair { fst : A ; snd : B fst }. (* primitive projections only *)
Variant False := . (* implies anything *)
Variant True := I. (* non-empty hprop *)
Inductive nat := O | S (_ : nat). (* fuel *)

Notation "A -> B" := (forall (_:A), B) (at level 99, right associativity, B at level 200) : type_scope.
Arguments exi [_] _.
Arguments pair {_ _}.
Notation "'exists' x .. y , p" := (exi (fun x => .. (exi (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'exists'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.
Notation "{ a  &  B }"
  := (exi (fun a => B%type))
       (at level 0, a at level 99)
     : type_scope.
Notation "{ a : A  &  B }"
  := (exi (fun a : A%type => B%type))
       (at level 0, a at level 99)
     : type_scope.
Infix "/\" := (fun A B : Type => { _ : A & B }) (at level 80, right associativity) : type_scope.
Infix "*" := (fun A B : Type => { _ : A & B }) (at level 40, left associativity) : type_scope.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.
Notation "0" := (False) : type_scope.
Notation "1" := (True) : type_scope.
Notation "0" := (O).
Notation "1" := (S 0).

Fixpoint eq_nat (a : nat) (b : nat) :=
  match a, b with
  | O, O => True
  | S a, S b => eq_nat a b
  | _, _ => False
  end.
Lemma eq_nat_refl a : eq_nat a a.
Proof. induction a; cbn; [exact I|assumption]. Defined.
Lemma eq_nat_sym {a} : forall {b}, eq_nat a b -> eq_nat b a.
Proof. induction a, b; cbn; eauto with nocore. Defined.
Lemma eq_nat_inj a b (_ : eq_nat (S a) (S b)) : eq_nat a b.
Proof. destruct a, b; eauto with nocore. Defined.
Lemma transport_nat a : forall b P (_ : eq_nat a b) (_ : P a), P b.
Proof.
  induction a, b;
         repeat match goal with
                | H : 0 |- _ => destruct H
                | H : 1 |- _ => destruct H
                | H : exi _ |- _ => destruct H
                | _ => progress intros
                | _ => progress cbn [eq_nat] in *
                | _ => assumption
                end.
  exact (IHa _ (fun n => P (S n)) X X0).
Defined.
Lemma transport_eq_nat a : forall b P (p q : eq_nat a b) (_ : P p), P q.
Proof. induction a;
         repeat match goal with
                | H : 0 |- _ => destruct H
                | H : 1 |- _ => destruct H
                | H : exi _ |- _ => destruct H
                | _ => progress intros
                | _ => progress cbn [eq_nat] in *
                | H : context [match ?n with O => _ | _ => _ end ] |- _ => destruct n
                | _ => assumption
                end.
       exact (IHa _ _ p _ X).
Defined.

(** [vec] is a one-parameter one-index family of inductive types.
    We will be implementing it in terms of 0 1 ∀ ∃ ℕ *)
Module Target.
  Section vec.
    Context {T : Type}.
    Inductive vec : nat -> Type :=
    | nil : vec 0
    | cons {n' : nat} (_ : T)  (_ : vec n') : vec (S n').
  End vec. Arguments vec : clear implicits.
End Target.

(** We can reduce inductive families to inductive types by enforcing index relationships using a recursive predicate. If equality of indices is decidable, the enforcement predicate is a hprop, allowing for the original dependent eliminator to be reconstructed without modification. *)
Module WithoutIndices.
  Section vec.
    Context {T : Type}.
    Inductive prevec : Type :=
    | prenil
    | precons (n : nat) (_ : T)  (_ : prevec).
    Fixpoint enforce (v : prevec) (n : nat) {struct v} :=
      match v with
      | prenil => eq_nat n 0
      | precons n' _ v' => eq_nat n (S n') /\ enforce v' n'
      end.
    Definition vec (n : nat) : Type := { v & enforce v n }.
    Definition nil : vec 0 := (prenil, I).
    Definition cons {n : nat} (x : T) (v : vec n) : vec (S n) := (precons n x (fst v), (@pair _ (fun _ => enforce _ _) (eq_nat_refl (S n)) (snd v))).

    Lemma vec_rect (n : nat) : forall (v : vec n) P (Pnil : P 0 nil) (Pcons : forall (n' : nat) (t : T) (v : vec n'), P n' v -> P (S n') (cons t v)), P n v.
    Proof.
      induction n; intros; destruct v as [[|n' x p'] []];
        try solve [contradiction | exact Pnil].
      pose proof (fun e' => Pcons n x (p', e') (IHn (p', e') _ Pnil Pcons)) as H; clear IHn Pcons Pnil.
      cbv [cons] in H; cbn [fst snd] in *.
      assert (eq_nat n n') as Hn by (apply eq_nat_inj; assumption).
      pattern n in H; eapply transport_nat in H; [|eapply Hn].
      specialize (H snd0).
      revert fst0; pattern n; eapply transport_nat; [exact (eq_nat_sym Hn)|]; intros.
      pattern (eq_nat_refl (S n')) in H; unshelve eapply transport_eq_nat in H; [exact fst0|].
      exact H.
    Defined.
  End vec. Arguments prevec : clear implicits. Arguments vec : clear implicits.
  Goal False.
    pose (vec nat : nat -> Set).
  Abort.
End WithoutIndices.

Module UsingNTypes.
  Section prevec.
    Context {T : Type}.
    (* Inductive prevec : Type :=
       | prenil
       | precons (n : nat) (_ : T)  (_ : prevec). *)
    Definition prevec_args (constructor : nat) (recurse : Type) : Type :=
      match constructor with
      | 0 => 1
      | 1 => nat * (T * recurse)
      | _ => 0
      end.
    Fixpoint prevec_fuel (f : nat) {struct f} : Type :=
      match f with
      | 0 => 0
      | S f => { tag & prevec_args tag (prevec_fuel f) }
      end.
    (* [canonical f pv] encodes the requirement that [f] is the
        minimum possible amount of fuel for constructing [pv] *)
    Fixpoint canonical (f : nat) {struct f} : prevec_fuel f -> Type :=
      match f with
      | 0 => fun _ => False
      | S f =>
        fun pv =>
          match fst pv as tag return prevec_args tag _ -> _ with
          | 0 => fun args => eq_nat f 0
          | 1 => fun args => canonical f (snd (snd args))
          (* recursive calls combine using propositional OR *)
          | _ => fun _ => False
          end (snd pv)
      end.
    Definition prevec := { f & { pvf : prevec_fuel f & canonical f pvf } }.
    Definition prenil : prevec := (1, ((0, I), I)).
    Definition precons (n : nat) (x : T) (pv : prevec) : prevec :=
      (* new fuel is computed as 1+max(fuels of subtrees) *)
      (S (fst pv), ((1, (n, (x, fst (snd pv)))), snd (snd pv))).
    Lemma prevec_rect p : forall
        (P : prevec -> Type)
        (Pprenil : P prenil)
        (Pprecons : forall (n : nat) (t : T) (p : prevec), P p -> P (precons n t p)),
        P p.
    Proof.
      destruct p as [f [r c]]; revert c; revert r; induction f;
        repeat match goal with
               | H : 0 |- _ => destruct H
               | H : 1 |- _ => destruct H
               | H : exi _ |- _ => destruct H
               | _ => assumption
               | H : context [match ?n with O => _ | _ => _ end ] |- _ => destruct n
               | _ => progress intros
               | _ => progress cbn [eq_nat canonical prevec_fuel prevec_args fst snd] in *
               end.
      { pose proof (eq_nat_sym c) as Hf.
        revert c. pattern f.
        eapply transport_nat; [eapply Hf|].
        intros c. pattern c.
        unshelve eapply transport_eq_nat.
        exact I.
        assumption. }
      { exact (Pprecons fst0 fst1 (_,(snd0, c)) (IHf snd0 c P ltac:(assumption) ltac:(assumption))). }
    Defined.
  End prevec.
End UsingNTypes.