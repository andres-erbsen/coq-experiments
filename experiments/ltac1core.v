Declare ML Module "ltac_plugin".
Local Set Default Proof Mode "Classic".

Ltac _assert_fails tac :=
  tryif tac then fail 0 tac "succeeds" else idtac.
Ltac _assert_succeeds tac :=
  tryif (_assert_fails tac) then fail 0 tac "fails" else idtac.
Tactic Notation "assert_succeeds" tactic3(tac) :=
  _assert_succeeds tac.
Tactic Notation "assert_fails" tactic3(tac) :=
  _assert_fails tac.

(** [texact t] first evaluates tactic [t] to a term and solves the current goal using that term. *)
Tactic Notation "texact" tactic(x) := exact x.

Ltac typeof x :=
  match type of x with
  | ?T => T
  end.
Global Notation typeof x := (ltac:(texact (typeof x))) (only parsing).

Ltac getgoal := match goal with |- ?G => G end.

Ltac _syntactic_apply_openconstr_of_type pf P :=
  let G := getgoal in
  first
    [ constr_eq P G; exact pf
    | lazymatch P with forall _, ?C => _syntactic_apply_openconstr_of_type open_constr:(pf _) C end ].
Ltac syntactic_apply pf :=
  unshelve _syntactic_apply_openconstr_of_type pf constr:(typeof pf).

Ltac __evarconv x y :=
  let __ := open_constr:(fun eq (eq_refl : forall a, eq a a) => (eq_refl _ : eq x y)) in idtac.
Ltac _evarconv x y := __evarconv x y || __evarconv y x.
Tactic Notation "evarconv" open_constr(x) open_constr(y) :=
  _evarconv x y.
(* Tactic Notation "unify" open_constr(x) open_constr(y) := fail "[unify] is deprecated in favor of evarconv, us instead: evarconv" x y. *)
  
Ltac _syntactic_unify_value x y :=
  match constr:(Set) with
  | _ => is_evar x; evarconv x y
  | _ => is_evar y; evarconv x y
  (* | _ => constr_eq x y *)
  | _ => lazymatch x with
         | ?f ?a => lazymatch y with ?g ?b => _syntactic_unify_value f g; _syntactic_unify_value a b end
         | (fun (a:?Ta) => ?f a)
           => lazymatch y with (fun (b:?Tb) => ?g b) =>
                               let __ := constr:(fun (a:Ta) (b:Tb) => ltac:(_syntactic_unify_value f g; exact Set)) in idtac end
         (* TODO: fail fast in more cases *)
         | _ => evarconv x y; constr_eq x y
         end
  end.
Ltac _syntactic_unify x y :=
  first
    [ constr_eq constr:(typeof x) constr:(typeof y)
    | _syntactic_unify constr:(typeof x) constr:(typeof y) ];
  _syntactic_unify_value x y.

Tactic Notation "syntactic_unify" open_constr(x) open_constr(y) :=
  _syntactic_unify x y.

Ltac _syntactic_eapply_openconstr_of_type pf P :=
  let G := getgoal in
  first
    [ syntactic_unify P G; change P; exact pf
    | lazymatch P with forall _, ?C => _syntactic_eapply_openconstr_of_type open_constr:(pf _) C end ].
Ltac syntactic_eapply pf :=
  unshelve _syntactic_eapply_openconstr_of_type pf constr:(typeof pf).

(** Deprecations of commonly used very broken tactics *)

Tactic Notation "simple" "apply" open_constr(x) := fail "[simple apply] uses more broken unification, instead use: syntactic_apply" x.
Tactic Notation "simple" "eapply" open_constr(x) := fail "[simple apply] uses more broken unification, instead use: syntactic_eapply" x.
Tactic Notation "apply" open_constr(x) := fail "[apply] messes with projections and uses more broken unification, instead use: syntactic_apply" x.
Tactic Notation "eapply" open_constr(x) := fail "[eapply] messes with projections uses more broken unification, instead use: syntactic_eapply" x.

Set SimplIsCbn.

Tactic Notation "intuition" := fail "[intuition] runs [auto with *], instead use: intuition idtac".
Tactic Notation "dintuition" := fail "[dintuition] runs [auto with *], instead use: intuition idtac".

Tactic Notation "auto" := fail "[auto] is superseded by [typeclasses eauto with core]".
Tactic Notation "auto" "using" constr_list(lems) := fail "[auto using] is superseded by [typeclasses eauto with core], use instead: pose proof" lems "; typeclasses eauto".
Tactic Notation "auto" "with" ref(db) := fail "[auto with] is superseded by [typeclasses eauto with core], use instead: typeclasses eauto with" db.
Tactic Notation "eauto" := fail "[eauto] is superseded by [typeclasses eauto with core]".
Tactic Notation "eauto" "using" constr_list(lems) := fail "[eauto using] is superseded by [typeclasses eauto with core], use instead: pose proof" lems "; typeclasses eauto".
Tactic Notation "eauto" "with" ref(db) := fail "[eauto with] is superseded by [typeclasses eauto with core], use instead: typeclasses eauto with" db.

Module _test.
  Inductive True : Prop := I.
  Inductive and {P Q : Prop} : Prop := conj (_:P) (_:Q).
  Global Arguments and : clear implicits.

  Goal True.
    pose proof (fun (a b c:and True True) => I) as pf.
    syntactic_apply pf;
      [ exact (conj I I)
      | exact (conj I I)
      | exact (conj I I) ].
  Qed.

  Goal True.
    pose proof (conj I I) as pf.
    assert_fails (syntactic_apply pf). (* should not automagically use projections *)
    exact I.
  Qed.

  Goal True.
    pose proof (I : (fun x => x) True) as pf.
    assert_fails (syntactic_apply pf). (* should not do reduction in hyps *)
    exact I.
  Qed.

  Goal (fun x => x) True.
    pose proof (I : True) as pf.
    assert_fails (syntactic_apply pf). (* should not do reduction in goal *)
    exact I.
  Qed.

  Goal True.
    assert_succeeds (syntactic_unify Type Type).
    assert_succeeds (syntactic_unify Set Set).
    assert_succeeds (syntactic_unify _ _).
    assert_succeeds (syntactic_unify _ Set).
    assert_succeeds (syntactic_unify Set _).
    assert_fails (syntactic_unify Set Type).
    assert_fails (syntactic_unify Prop Type).
    assert_succeeds (syntactic_unify (fun (x : Prop) => Set) (fun (_ : _) => _)).
    assert_fails (syntactic_unify (fun (x : Prop) => Set) (fun (_ : Type) => _)).
    exact I.
  Qed.

  Goal True.
    assert_succeeds (evarconv Set Set).
    assert_succeeds (evarconv Type Type).
    assert_succeeds (let x := open_constr:(_) in evarconv Set x).
    assert_succeeds (let x := open_constr:(_) in evarconv x Set).
    assert_succeeds (let x := open_constr:(_) in evarconv I x).
    assert_succeeds (let x := open_constr:(_) in evarconv x I).
    exact I.
  Abort.

  Goal True.
    let x := open_constr:(_) in
    syntactic_unify x I;
      lazymatch x with
      | I => exact I
      end.
  Qed.

  Goal True.
    let x := open_constr:(I) in
    let y := open_constr:(_) in
    let tx := typeof x in
    let ty := typeof y in
    evarconv ty tx.

    let x := open_constr:(I) in
    let y := open_constr:(_) in
    let tx := typeof x in
    let ty := typeof y in
    evarconv tx ty.
  _syntactic_unify_value x y.
    _syntactic_unify I x;
      lazymatch x with
      | I => exact I
      end.
  Qed.

  Goal True.
    let x := open_constr:(_) in
    syntactic_unify (fun (t:True) => conj I I) (fun (y:True) => x);
      lazymatch x with
      | conj I I => exact I
      end.
  Qed.

  Goal True.
    assert_fails (syntactic_unify (fun (t:True) => I) (fun (y:True) => (fun x => x) I)). (* should not do reduction (beta) *)
    exact I.
  Qed.

  Goal True.
    assert_fails (syntactic_unify (match conj I I with conj a b => I end) I). (* should not do reduction (match) *)
    exact I.
  Qed.

  Goal True.
    evar (p : Prop).
    eassert (and p True). {
      assert_fails (syntactic_eapply (conj I I)). (* should not do reduction (unfold p) *)
      subst p; syntactic_eapply (conj I I). }
    let p := (eval cbv [p] in p) in
    constr_eq p True.
    exact I.
  Qed.

  Goal True.
    evar (p : Prop).
    assert (and p True). {
      change (and p ((fun x => x) True)).
      assert_fails (syntactic_eapply (conj I I)). (* should not do reduction (unfold p) *)
      assert_fails (syntactic_eapply (conj I I)). (* should not do reduction (beta) *)
      subst p; syntactic_eapply (conj I I : (and ((fun x => x) True) ((fun x => x) True))). }
    let p := (eval cbv [p] in p) in
    constr_eq p ((fun x => x) True) (* intended behavior *)
    || constr_eq p True. (* current behavior *)
    exact I.
  Qed.
End _test.