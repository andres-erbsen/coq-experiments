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
  Definition ok_for (T : Type) : prop := T -> prop.
  Existing Class ok_for.
  Definition ok {T} {ok_T:ok_for T} := ok_T.
  Existing Class ok.

  Definition eq_for (T : Type) : prop := T -> T -> prop.
  Existing Class eq_for.
  Definition eq {T} {eq_T:eq_for T} := eq_T.
  Global Infix "=" := eq (at level 70, no associativity).
End value.

Module prop.
  Notation prop := prop.

  Definition unsatisfiable : prop := forall P : prop, P.
  Definition trivial : prop := forall P : prop, P -> P.
  (* Notation False := unsatisfiable. *)
  (* Notation True := trivial. *)

  Global Instance ok : ok_for prop :=
    fun _ => trivial.

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

Module eq.
  Section eq.
    Context {T} {ok_T : ok_for T}.
    Record equivalence {eq_T : eq_for T} :=
      {
        refl : forall (x : T), ok_T x -> eq_T x x;
        symm : forall (x y : T), ok_T x -> ok_T y -> eq_T x y -> eq_T y x;
        trans : forall (x y z : T), ok_T x -> ok_T y -> ok_T z
                                    -> eq_T x y -> eq_T y z -> eq_T x z;
      }.
    Global Arguments equivalence : clear implicits.
    Global Instance ok : ok_for (eq_for T) := equivalence.

    Global Instance eq : eq_for (eq_for T) :=
      fun eq1 eq2 => forall x y, prop.iff (eq1 x y) (eq2 x y).
  End eq.
End eq.

Module canonical.
  Module eq.
    Section eq.
      Context {A : Type}.
      Inductive eq (x : A) : forall (y : A), prop :=
        refl : eq x x.
      Context { irrelevant_ok_A : ok_for A }.
      Definition ok : eq.ok eq :=
        {| Top.eq.refl := fun x _ => refl x;
           eq.symm := fun x y _ _  (pf : eq x y)
                      => match pf with refl _ => refl x end;
           eq.trans := fun x y z _ _ _ (pf : eq x y)
                       => match pf with refl _ => fun x => x end |}.
    End eq.
  End eq.
  Notation eq := eq.eq.
  (* Notation eq_refl := eq.refl *)
End canonical.

Module arrow.
  Section arrow.
    Context {A : Type} {ok_A : ok_for A} {eq_A : eq_for A}.
    Context {B : Type} {ok_B : ok_for B} {eq_B : eq_for B}.

    Global Instance ok : ok_for (A -> B) :=
      fun f => prop.and (forall a, ok_B (f a)) (forall a1 a2, ok_A a1 -> ok_A a2 -> eq_A a1 a2 -> eq_B (f a1) (f a2)).

    Global Instance eq : eq_for (A -> B) :=
      fun f g => forall a, ok_A a -> eq_B (f a) (g a).
  End arrow. 
End arrow. 

Require Coq.Init.Prelude. (* TODO: figure out what to do about stdlib tactics *)
Module prop_instances.
  Module iff.
    Import prop.iff.
    Global Instance ok_eq : ok prop.eq :=
      {|
        eq.refl := fun P _ => {| right := fun x => x; left := fun x => x |};
        eq.symm := fun P Q _ _ pq => {| right := pq.(left); left := pq.(right) |};
        eq.trans := fun P Q R _ _ _ pq qr => {| right := fun p => qr.(right) (pq.(right) p); left := fun r => pq.(left) (qr.(left) r) |};
      |}.
  End iff.

  Import Coq.Init.Prelude.
  (* TODO: do not unfold [arrow.ok] to avoid quadratic blowup *)

  Module not.
    Global Instance ok : ok prop.not.
    Proof. (* FIXME *)
      cbv [prop.not prop.unsatisfiable];
        firstorder;
        repeat match goal with
               | [H : forall P, P |- _ ] => apply H
               end.
    Qed.
  End not.

  Module and.
    Import prop.and.
    Global Instance ok : ok and. Proof. firstorder. Qed.
  End and.

  Module or.
    Import prop.or.
    Global Instance ok : ok or. Proof. firstorder. Qed.
  End or.
End prop_instances.

Module subset.
  Definition subset (T : Type) (P : T -> prop) := T.
  Global Instance ok T P {ok_T : ok_for T} : ok_for (subset T P) :=
    fun x => prop.and (ok_T x) (P x).
  Global Instance eq T P {eq_T : eq_for T} : eq_for (subset T P) :=
    fun x y => eq_T x y.
End subset.
Notation subset := subset.subset.

Module quotient.
  Definition quotient (T : Type) (R : T -> T -> prop) := T.
  Global Instance ok T R {ok_T : ok_for T} : ok_for (quotient T R) :=
    fun x => ok_T x.
  Global Instance eq T R {eq_T : eq_for T} : eq_for (quotient T R) :=
    fun x y => prop.or (eq_T x y) (R x y).
End quotient.
Notation quotient := quotient.quotient.

Module int.
  Record sig :=
    mk
    {
      int : Type;
      ok_for_int : ok_for int;
      eq_for_int : eq_for int;

      zero : int;
      succ : int -> int;
      pred : int -> int;
    }.
  Global Existing Instance ok_for_int.
  Global Existing Instance eq_for_int.

  Record spec (s:sig) : prop :=
    {
      ok_eq : ok s.(eq_for_int);

      ok_zero : ok s.(zero);
      ok_succ : ok s.(succ);
      ok_pred : ok s.(pred);

      pred_succ : forall i, s.(pred) (s.(succ) i) = i;
      succ_pred : forall i, s.(succ) (s.(pred) i) = i;
    }.
  Global Instance ok : ok_for sig := fun s => spec s.

  Module unary_impl.
    Inductive int : Type :=
    | zero : int
    | succ : int -> int
    | pred : int -> int.

    Definition canonicalize : int -> int :=
      (int_rect _)
        zero
        (fun _ m => match m with pred m' => m' | _ => succ m end)
        (fun _ m => match m with succ m' => m' | _ => pred m end).

    Global Instance ok : ok_for int :=
      fun _ => prop.trivial.

    Global Instance eq : eq_for int :=
      fun (n m : int) => canonical.eq (canonicalize n) (canonicalize m).

    Definition neg : int -> int :=
      (int_rect _)
        zero
        (fun _ => pred)
        (fun _ => succ).

    Definition abs (n : int) :=
      match canonicalize n with
      | pred _ => neg n
      | _ => n
      end.
  End unary_impl.

  Definition unary : sig :=
    {|
      int := unary_impl.int;

      zero := unary_impl.zero;
      succ := unary_impl.succ;
      pred := unary_impl.pred;
    |}.

  Module unary.
    Global Instance ok : value.ok unary. Admitted.
  End unary.
End int.

(* TODO: pair *)

Goal prop.unsatisfiable.
  Local Notation int := (int.unary.int).
  pose (_ : ok_for (int -> int)) as ok_int_int; cbv [ok arrow.ok] in ok_int_int.
  pose (_ : eq_for (int -> int)) as eq_int_int; cbv [eq arrow.eq] in eq_int_int.
  pose (_ : ok_for (subset (int -> int) (fun f => int.unary.eq (f int.unary.zero) int.unary.zero))) as ok_int_int_00; cbv [ok arrow.ok subset.ok] in ok_int_int_00.
  pose (_ : eq_for (quotient int (fun a b => int.unary.eq (int.unary.abs a) (int.unary.abs b)))) as REQUIRES_FILTERED_UNIFICATION_eq_absint; cbv [eq quotient.eq] in REQUIRES_FILTERED_UNIFICATION_eq_absint.
  pose (_ : ok_for (quotient int (fun a b => int.unary.eq (int.unary.abs a) (int.unary.abs b)) -> int)) as ok_absint_int; cbv [ok arrow.ok quotient.ok] in ok_absint_int.
Abort.
