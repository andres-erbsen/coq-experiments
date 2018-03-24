Declare ML Module "ltac_plugin".
Local Set Default Proof Mode "Classic".

Unset Universe Minimization ToSet.
Set Universe Polymorphism.
Unset Refine Instance Mode.
Set Keyed Unification.
Set Suggest Proof Using.

Unset Printing Dependent Evars Line.
Set Printing Depth 2097152.

(* For Prop:
Set Keep Proof Equalities.
*)

(* For inductives:
Set Primitive Projections.
Unset Printing Primitive Projection Parameters.
Set Printing Projections.
Set Case Analysis Schemes.
Set Nonrecursive Elimination Schemes.
Set Decidable Equality Schemes.
Set Boolean Equality Schemes.
Unset Program Cases.
*)

(* TODO: investigate these two:
Set Typeclasses Strict Resolution.
Set Typeclasses Filtered Unification.
*)

(* TODO: implement Set Default Goal Selector "unique"
Set Default Goal Selector "all".
*)

Delimit Scope type_scope with type.
Bind Scope type_scope with Sortclass.
Notation "A -> B" := (forall (_:A), B) (at level 99, right associativity, B at level 200) : type_scope.

Definition prop := Type.
Bind Scope type_scope with prop.

Module Export relations.
  Definition relation_for (A B : Type) : prop := A -> B -> prop.
  Existing Class relation_for.
  Global Notation eq_for T := (relation_for T T).
  Definition eq {T} {eq_T : eq_for T} := eq_T.
  Global Infix "=" := eq (at level 70, no associativity).
  Definition ok {T} {eq_T : eq_for T} (x : T) := x = x.

  Global Instance relation_forall {F F' : Type -> Type}
         (RF : forall A A', relation_for A A' -> relation_for (F A) (F' A'))
    : relation_for (forall X : Type, F X) (forall X : Type, F' X)
    := fun g g' => forall (A A' : Type) (R : relation_for A A'),
           RF A A' R (g A) (g' A').

  Global Instance relation_arrow
         {A A' : Type} (RA : relation_for A A')
         {B B' : Type} (RB : relation_for B B')
    : relation_for (A -> B) (A' -> B')
    := fun f g => forall x y, RA x y -> RB (f x) (g y).
End relations.

Module prod.
  Definition prod A B := forall T, (A -> B -> T) -> T.
  Definition eq {A B} (eq_A : eq_for A) (eq_B : eq_for B) : eq_for (prod A B) := _.
End prod.
Notation prod := prod.prod.

Module sum.
  Definition sum A B := forall T, (A -> T) -> (B -> T) -> T.
  Definition eq {A B} (eq_A : eq_for A) (eq_B : eq_for B) : eq_for (sum A B) := _.
End sum.
Notation sum := sum.sum.

Module prop.
  Notation prop := prop.

  Definition unsatisfiable : prop := forall P : prop, P.
  Definition trivial : prop := forall P : prop, P -> P.
  Definition and P Q := Eval cbv beta delta [prod] in (prod P Q).
  Definition or P Q := Eval cbv beta delta [sum] in (sum P Q).
  Global Instance eq : eq_for prop :=
    fun P Q => and (P -> Q) (Q -> P).
  Notation iff := eq.
End prop.
Global Infix "<->"  := prop.iff (at level 95, right associativity) : type_scope.
Global Infix "\/"  := prop.or (at level 85, right associativity) : type_scope.
Global Infix "/\"  := prop.and (at level 80, right associativity) : type_scope.

Module unit.
  Definition unit := forall T, T -> T.
  Global Instance eq : eq_for unit := _.

  Definition tt : unit := fun (T : Type) (x : T) => x.
  Lemma tt_ok : ok tt. Proof. cbv; intros; assumption. Qed.

  Lemma eq_sym a b (eq_a_b : eq a b) : eq b a.
  Proof. cbv in *; intros. refine (eq_a_b _ _ (fun a b => _ b a) _ _ _). assumption; fail "unreachable". Abort.

  Lemma unit_cases (u : unit) (ok_u : ok u) : eq u tt.
  Proof.
    cbv in *; intros.
    refine (ok_u _ _ (fun a b => R a y) x y _); assumption.
  Qed.

  Lemma unit_rect (P : unit -> prop) (ok_P : ok P) (Ptt : P tt) (u : unit) (ok_u : ok u) : P u.
  Proof.
    pose proof unit_cases.
    refine (ok_P _ _ _ _ _); typeclasses eauto with nocore.
  Qed.
End unit.
Notation unit := unit.unit.

Module bool.
  Definition bool : Type := forall (T : Type), T -> T -> T.
  (*
  Inductive eq : eq_for bool :=
  | eq_true_true : eq true true
  | eq_false_false : eq false false.
  Global Existing Instance eq.
  *)
  Global Instance eq : eq_for bool := _.

  Definition true : bool := fun (T : Type) (x y : T) => x.
  Lemma ok_true : ok true. Proof. cbv; intros; assumption. Qed.
  Definition false : bool := fun (T : Type) (x y : T) => y.
  Lemma ok_false : ok false. Proof. cbv; intros; assumption. Qed.
  Definition ite {T} (b:bool) (x y : T) : T := b _ x y.
  Lemma ok_ite {T} {eqT : eq_for T} : ok (@ite T).
  Proof. cbv -[bool] in *. intros ? ? H; intros.
         refine (H _ _ _ _ _ _ _ _ _); assumption. Qed.

  (* FIXME: Global Instance *)
  Lemma eq_sym a b (eq_a_b : eq a b) : eq b a.
  Proof. cbv in *; intros. refine (eq_a_b _ _ (fun u v => R v u) _ _ X _ _ X0). Qed.

  Lemma ite_true_false b (ok_b : ok b) : ite b true false = b.
  Proof.
    pose proof ok_true as ok_true.
    pose proof ok_false as ok_false.
    cbv -[bool true false] in *; intros.
    pose proof fun (X:=X) (Y:=X0) => ok_b _ _ (fun x y => R x y) x y X x0 y0 Y as H; cbn in H.
    change (R ( b                  A x x0) (b A' y y0)) in H.
    change (R ((b bool true false) A x x0) (b A' y y0)).
  Admitted.

  Lemma bool_cases (b : bool) (ok_b : ok b)
    : b = true \/ b = false.
  Proof.
    pose proof
         (ok_b bool bool (fun x y => (x = true) \/ (x = false))%type
         true false (fun x pf _ => pf ok_true)
         false true (fun x _ pf => pf ok_false)
         : ite b true false = true \/ ite b true false = false) as Htf.
  Admitted.

  Lemma bool_rect
             (P : bool -> prop) (ok_P : ok P)
             (_ : P true) (_ : P false)
             (b : bool) (ok_b : ok b)
    : P b.
  Proof.
    refine (bool_cases b ok_b _ _ _); intros Heq;
      refine (ok_P _ _ Heq _ _); typeclasses eauto with nocore.
  Qed.
End bool.