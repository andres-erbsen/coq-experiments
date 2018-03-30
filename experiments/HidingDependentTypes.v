Require Import Coq.derive.Derive.
Require Import Coq.Program.Tactics.
Require Import Coq.Classes.Morphisms.

Module predicate.
  Definition predicate A := A -> Prop.
  Definition eq {A} : predicate A -> predicate A -> Prop := (pointwise_relation _ iff)%signature.
  Definition exactly {A} (a : A) := fun b => Logic.eq b a.
  Definition any A := fun (a : A) => True.
  Definition bind {A B} (pa : predicate A) (Rab : A -> predicate B) : predicate B :=
    fun b => exists a, pa a /\ Rab a b.

  Global Instance Proper_exactly {A} : Proper (Logic.eq ==> eq) (@exactly A).
  Proof. cbv. intuition congruence. Qed.
  Global Instance Proper_bind {A B}
    : Proper (eq ==> (pointwise_relation _ eq) ==> eq) (@bind A B).
  Proof.
    repeat (cbv||intros||subst||destruct_one_pair||destruct_one_ex||split);
      (eexists; split; [eapply H | eapply H0]; typeclasses eauto with core).
  Qed.

  Definition functional {A} (pa : predicate A) :=
    forall x y, pa x -> pa y -> x = y.
  Global Instance Proper_functional_flipimpl {A} : Proper (pointwise_relation _ Basics.impl --> Basics.impl) (@functional A).
  Proof. cbv; typeclasses eauto with core. Qed.
  Global Instance Proper_functional {A} : Proper (eq ==> iff) (@functional A).
  Proof.
    intros ???. cbv [eq pointwise_relation] in *. 
    split; eapply Proper_functional_flipimpl;
      cbv [Basics.flip pointwise_relation Basics.impl];
      eapply H.
  Qed.
  Lemma functional_exactly {A} a : functional (@exactly A a).
  Proof. cbv. congruence. Qed.
  Lemma functional_bind
        {A} pa (Hpa : @functional A pa)
        {B} Rab (HRab : forall pa, @functional B (bind pa Rab))
    : functional (bind pa Rab).
  Proof. cbv in *; intros. eapply HRab; typeclasses eauto with core. Qed.

  Module _examples.
    Local Definition safe_div : forall (a b : nat), b <> 0 -> nat
      := fun a b pf => Nat.div a b.
    
    Derive
      simple_div
    SuchThat
      (forall a b pf, simple_div a b = safe_div a b pf)
    As simple_div_correct.
    Proof. intros. cbv [safe_div]. subst simple_div. reflexivity. Qed.
    
    Local Opaque simple_div safe_div.
    
    Local Definition safe_mediant ab cd (H: snd ab + snd cd <> 0) : nat :=
      match fst ab, snd ab with a, b =>
      match fst cd, snd cd with c, d =>
      safe_div (a+c) (b+d) H
      end end.

    Derive
      simple_mediant
    SuchThat
      (forall ab cd pf, simple_mediant ab cd = safe_mediant ab cd pf)
    As simple_mediant_correct.
    Proof.
      (* 1) Prove `On X x`       # purely syntax directed *)
      evar (predicate_safe : nat*nat -> nat*nat -> predicate nat).
      assert (predicate_safe_correct : forall ab cd pf, predicate_safe ab cd (safe_mediant ab cd pf)).
      { let ev := eval unfold predicate_safe in predicate_safe in
            unify ev
              (fun ab cd => bind (any _) (fun H => exactly (safe_mediant ab cd H))).
        cbv; typeclasses eauto with core. }

      (* 2) Prove `Functional X` # purely syntax directed *)
      assert (functional_predicate_safe :
                forall ab cd, functional (predicate_safe ab cd)).
      { repeat (cbv||intros||subst||destruct_one_pair||destruct_one_ex||split). }

      (* 3) Prove `Ish_eq X Y`   # this doesn't have dependent types *)
      (* TODO: does this actually not have dependent types? *)
      evar (predicate_simple : nat*nat -> nat*nat -> predicate nat).
      assert (eq_simple_safe : forall ab cd (H:snd ab + snd cd <> 0), eq (predicate_simple ab cd) (predicate_safe ab cd)).
      { intros ab cd H.
        cbv [predicate_simple].

        evar (func_simple : nat*nat -> nat*nat -> nat);
        let ev := eval unfold predicate_simple in predicate_simple in
            unify ev (fun ab cd => exactly (func_simple ab cd)).
        cbv [exactly func_simple].

        cbv [predicate.eq pointwise_relation].

        cbv [predicate_safe].

        cbv [any exactly bind].

        cbv [safe_mediant].

        let ev := eval unfold func_simple in func_simple in
            unify ev
              (fun ab cd =>
                   match fst ab, snd ab with a, b =>
                   match fst cd, snd cd with c, d =>
                   simple_div (a+c) (b+d)
                   end end).
        cbv [predicate_simple  any exactly bind].
        repeat (intros||subst||destruct_one_pair||destruct_one_ex||split).
        exists H.
        repeat (intros||subst||destruct_one_pair||destruct_one_ex||split).
      }

      (* 4) Prove `On Y y`       # purely syntax directed *)
      assert (predicate_simple_correct : forall ab cd, predicate_simple ab cd (simple_mediant ab cd)).
      { intros. cbv [predicate_simple exactly]. subst simple_mediant. reflexivity. }

      (* 5) glue... *)
      intros.
      eapply functional_predicate_safe; [|eapply predicate_safe_correct].
      eapply eq_simple_safe; eauto.
    Qed.
  End _examples.
End predicate.