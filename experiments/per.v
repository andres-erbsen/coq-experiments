Declare ML Module "ltac_plugin".
Local Set Default Proof Mode "Classic".

(* Set Default Goal Selector "all". (* intentionally annoying *) *)

Set Keyed Unification.

Set Suggest Proof Using.
Unset Refine Instance Mode.

Unset Universe Minimization ToSet.
Set Universe Polymorphism.

Set Case Analysis Schemes.
Set Nonrecursive Elimination Schemes.
Set Decidable Equality Schemes.
Set Boolean Equality Schemes.
Unset Program Cases.

Set Keep Proof Equalities.

Set Primitive Projections.
Unset Printing Primitive Projection Parameters.
Set Printing Projections.

Set Typeclasses Filtered Unification.
Set Typeclasses Strict Resolution.

Unset Printing Dependent Evars Line.
Set Printing Depth 2097152.

Local Notation "A -> B" := (forall (_:A), B) (at level 99, right associativity, B at level 200).

Definition prop := Type.

Module Export value.
  Definition eq_for (T : Type) : prop := T -> T -> prop.
  Existing Class eq_for.
  Definition eq {T} {eq_T : eq_for T} := eq_T.
  Global Infix "=" := eq (at level 70, no associativity).
  Definition ok {T} {eq_T : eq_for T} (x : T) := x = x.
End value.

Module arrow.
  Section arrow.
    Context {A : Type} {eq_A : eq_for A}.
    Context {B : Type} {eq_B : eq_for B}.
    Global Instance eq : eq_for (A -> B) :=
      fun f g => forall x y, eq_A x y -> eq_B (f x) (g y).
  End arrow. 
End arrow. 


Module prop.
  Notation prop := prop.

  Definition unsatisfiable : prop := forall P : prop, P.
  Definition trivial : prop := forall P : prop, P -> P.
  (* Notation False := unsatisfiable. *)
  (* Notation True := trivial. *)

  (* TODO: decide whether prop-s should be encoded as raw inductive types *)

  Module Import iff.
    Record iff {P Q : prop} : prop := mk { right : P -> Q; left : Q -> P }.
    Global Arguments iff : clear implicits.
  End iff.
  Notation iff := iff.iff.
  Global Instance eq : eq_for prop := iff.

  Definition not (P : prop) : prop := P -> unsatisfiable.

  Module and.
    Record and {P Q : prop} : prop := mk { left : P; right : Q }.
    Global Arguments and : clear implicits.
  End and.
  Notation and := and.and.

  Module or.
    Variant or {P Q : prop} : prop := left (_:P) | right (_:Q).
    Global Arguments or : clear implicits.
  End or.
  Notation or := or.or.
End prop.

Module bool.
  Definition bool : Type := forall (T : Type), T -> T -> T.
  (*
  Inductive eq : eq_for bool :=
  | eq_true_true : eq true true
  | eq_false_false : eq false false.
  Global Existing Instance eq.
  *)
  Global Instance eq : eq_for bool :=
    (* for [a -> a -> a] from http://www-ps.iai.uni-bonn.de/cgi-bin/free-theorems-webui.cgi *)
    fun (f1 f2 : bool) =>
      forall (T1 T2 : Type) (R : T1 -> T2 -> prop)
             x y (Rxy : R x y)
             z v (Rxy : R z v),
        R (@f1 T1 x z) (@f2 T2 y v).

  Definition true : bool := fun (T : Type) (x y : T) => x.
  Lemma ok_true : ok true. Proof. cbv; intros; assumption. Qed.
  Definition false : bool := fun (T : Type) (x y : T) => y.
  Lemma ok_false : ok false. Proof. cbv; intros; assumption. Qed.

  Lemma bool_rect
             (P : bool -> prop) (ok_P : ok P)
             (_ : P true) (_ : P false)
             (b : bool) (ok_b : ok b)
    : P b.
  Proof.
  Abort.

  Lemma bool_cases (b : bool) (ok_b : ok b)
    : prop.or (eq b true) (eq b false).
  Proof.
    (*
    destruct (bool_cases b ok_b); 
      exact (prop.iff.left (ok_P b _ ltac:(eassumption)) ltac:(eassumption)).
     *)
  Abort.
End bool.
