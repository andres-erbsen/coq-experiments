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
Global Notation "'typeof!' x" := (ltac:(texact (typeof x))) (only parsing, at level 10).

Global Notation "'subst!' y 'for' x 'in' f" := (match y with x => f end) (at level 10, f at level 200).

Ltac beta1 x :=
  lazymatch x with
  | (fun a => ?f) ?b => constr:(subst! b for a in f)
  end.
Global Notation "'beta1!' x" := (ltac:(texact (beta1 x))) (only parsing, at level 10).

Ltac zeta1 x :=
  lazymatch x with
  | let a := ?b in ?f => constr:(subst! b for a in f)
  end.
Global Notation "'zeta1!' x" := (ltac:(texact (zeta1 x))) (only parsing, at level 10).

Ltac delta1 x :=
  let y := eval unfold x in x in y.
Global Notation "'delta1!' x" := (ltac:(texact (delta1 x))) (only parsing, at level 10).

(* TODO: one-step match? *)
(* TODO: one-step fixpoint? *)
(* TODO: one-step delta-fixpoint-undelta?? *)
(* unlikely to be supported: one-step reduction of cofixpoints *)

Ltac getgoal _ := match goal with |- ?G => G end.

Ltac _evarconv x y :=
  let __ := open_constr:(fun eq (eq_refl : forall a, eq a a) => (eq_refl _ : eq x y)) in idtac.
Tactic Notation "evarconv" open_constr(x) open_constr(y) :=
  _evarconv x y.

(* kitchen sink of all unification methods *)
Ltac _unify x y := evarconv x y || evarconv y x || unify x y || unify y x.
Tactic Notation "unify" open_constr(x) open_constr(y) := unify x y.
(* Tactic Notation "unify" open_constr(x) open_constr(y) := fail "[unify] is deprecated in favor of evarconv, us instead: evarconv" x y. *)

Ltac _syntactic_unify x y :=
  match constr:(Set) with
  | _ => is_evar x; unify x y
  | _ => is_evar y; unify x y
  | _ => lazymatch x with
         | ?f ?a => lazymatch y with ?g ?b => _syntactic_unify f g; _syntactic_unify a b end
         | (fun (a:?Ta) => ?f a)
           => lazymatch y with (fun (b:?Tb) => ?g b) =>
                               let __ := constr:(fun (a:Ta) (b:Tb) => ltac:(_syntactic_unify f g; exact Set)) in idtac end
         | let a : ?Ta := ?v in ?f a
           => lazymatch y with let b : ?Tb := ?w in ?g b =>
                               _syntactic_unify v w;
                               let __ := constr:(fun (a:Ta) (b:Tb) => ltac:(_syntactic_unify f g; exact Set)) in idtac end
         (* TODO: fail fast in more cases *)
         | _ => unify x y; constr_eq x y
         end
  end.
Tactic Notation "syntactic_unify" open_constr(x) open_constr(y) :=
  _syntactic_unify x y.

Ltac _syntactic_unify_type_first x y :=
  first
    [ constr_eq constr:(typeof! x) constr:(typeof! y)
    | _syntactic_unify_type_first constr:(typeof! x) constr:(typeof! y) ];
  _syntactic_unify x y.
Tactic Notation "syntactic_unify_type_first" open_constr(x) open_constr(y) :=
  _syntactic_unify_type_first x y.

Ltac _syntactic_eapply_openconstr pf :=
  let P := typeof pf in
  let G := getgoal Set in
  first
    [ syntactic_unify P G; change P; exact pf
    | lazymatch P with forall __, ?C => _syntactic_eapply_openconstr open_constr:(pf _) end ].
Ltac _syntactic_eapply pf :=
  unshelve _syntactic_eapply_openconstr pf; shelve_unifiable.
Tactic Notation "syntactic_eapply" open_constr(pf) :=
  _syntactic_eapply pf.

Ltac _syntactic_apply_openconstr pf :=
  let P := typeof pf in
  let G := getgoal Set in
  match constr:(Set) with
  | _ => let __ := constr:(ltac:(_syntactic_unify P G; exact Set)) in
         open_constr:(pf)
  | _ => lazymatch P with
           forall __:?T, ?C =>
           lazymatch open_constr:(_:T) with
             ?e =>
             let pf := _syntactic_apply_openconstr open_constr:(pf e) in
             let __ := constr:(ltac:(assert_fails(has_evar T); exact Set)) in
             open_constr:(pf)
           end
         end
  end.
Ltac _syntactic_apply pf :=
  unshelve (idtac; let pf := _syntactic_apply_openconstr pf in exact pf).
Tactic Notation "syntactic_apply" open_constr(pf) :=
  _syntactic_apply pf.

Ltac _evarconv_eapply_rec pf :=
  match constr:(Set) with
  | _ => let pf := open_constr:(pf _) in _evarconv_eapply_rec pf
  | _ => exact pf
  end.
Ltac _evarconv_eapply pf := unshelve (_evarconv_eapply_rec pf); shelve_unifiable.
Tactic Notation "evarconv_eapply" open_constr(pf) :=
  _evarconv_eapply pf.

Ltac _evarconv_apply_rec pf :=
  match constr:(Set) with
  | _ =>
    let e := open_constr:(_) in
    let pf := _evarconv_apply_rec open_constr:(pf e) in
    let __ := constr:(ltac:(assert_fails (is_evar e); exact Set)) in
    constr:(pf)
  | _ => let G := getgoal Set in
         let P := typeof pf in
         let __ := constr:(ltac:(evarconv G P; exact Set)) in
         constr:(pf)
  end.
Ltac _evarconv_apply pf := unshelve (idtac; let pf := _evarconv_apply_rec pf in exact pf).
Tactic Notation "evarconv_apply" open_constr(pf) :=
  _evarconv_apply pf.

(** Deprecations of commonly used very broken tactics *)

Tactic Notation "simple" "apply" open_constr(x) := fail "[simple apply] uses more broken unification, instead use: syntactic_apply" x ". Alternatively, instead use: evarconv_apply" x.
Tactic Notation "simple" "eapply" open_constr(x) := fail "[simple apply] uses more broken unification, instead use: syntactic_eapply" x ". Alternatively, instead use: evarconv_eapply" x.
Tactic Notation "apply" open_constr(x) := fail "[apply] messes with projections and uses more broken unification, instead use: syntactic_eapply" x ". Alternatively, instead use: evarconv_apply" x.
Tactic Notation "eapply" open_constr(x) := fail "[eapply] messes with projections uses more broken unification, instead use: syntactic_eapply" x ". Alternatively, instead use: evarconv_eapply" x.

Set SimplIsCbn.

Tactic Notation "intuition" := fail "[intuition] runs [auto with *], instead use: intuition idtac".
Tactic Notation "dintuition" := fail "[dintuition] runs [auto with *], instead use: intuition idtac".

Tactic Notation "firstorder" := fail "[firstorder] runs [auto with *], instead use firstorder with core".

Tactic Notation "reflexivity" := fail "[reflexivity] uses more broken unification, instead use: exact Logic.eq_refl. When typeclass resolution is desired, instead use: exact (Coq.Classes.RelationClasses.reflexivity _)".

Tactic Notation "auto" := fail "[auto] is superseded by [typeclasses eauto with core]".
Tactic Notation "auto" "using" constr_list(lems) := fail "[auto using] is superseded by [typeclasses eauto with core], use instead: pose proof" lems "; typeclasses eauto".
Tactic Notation "auto" "with" ref(db) := fail "[auto with] is superseded by [typeclasses eauto with core], use instead: typeclasses eauto with" db.
Tactic Notation "eauto" := fail "[eauto] is superseded by [typeclasses eauto with core]".
Tactic Notation "eauto" "using" constr_list(lems) := fail "[eauto using] is superseded by [typeclasses eauto with core], use instead: pose proof" lems "; typeclasses eauto".
Tactic Notation "eauto" "with" ref(db) := fail "[eauto with] is superseded by [typeclasses eauto with], use instead: typeclasses eauto with" db.

Tactic Notation "unfold" constr_list(x) := fail "[unfold]: [cbn], [cbv], and [delta1] are recommended instead: cbv delta [" x "].".

Module _test.
  Section WithAnd.
    Context (True : Prop) (I : True).
    Context (and : forall P Q : Prop, Prop) (conj : forall (P Q : Prop) (_:P) (_:Q), and P Q).
    Local Arguments conj {_ _} _ _.

    Ltac constr_I := constr:(I).
    Goal True.
      texact constr_I.
    Qed.

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
      assert_succeeds (syntactic_unify (let x := Set in Prop) (let x := Set in Prop)).
      assert_succeeds (syntactic_unify (let x := Set in x) (let x := Set in x)).
      assert_fails (syntactic_unify (let x := Set in x) (let x := Set in Set)).
      assert_succeeds (syntactic_unify (fun (x : Prop) => Set) (fun (_ : _) => _)).
      assert_fails (syntactic_unify (fun (x : Prop) => Set) (fun (_ : Type) => _)).
      exact I.
    Qed.

    Goal True.
      assert_succeeds (evarconv Set Set).
      assert_succeeds (evarconv Type Type).
      assert_succeeds (idtac; let x := open_constr:(_) in evarconv Set x).
      assert_succeeds (idtac; let x := open_constr:(_) in evarconv x Set).
      assert_succeeds (idtac; let x := open_constr:(_) in evarconv I x).
      assert_succeeds (idtac; let x := open_constr:(_) in evarconv x I).
      exact I.
    Qed.

    Goal True.
      let x := open_constr:(_) in
      syntactic_unify x I;
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

    Goal forall P eq (H: forall (x:True) (Hx:eq x x), P) (HH:eq I I), P.
      intros.
      assert_fails (syntactic_apply H).
      syntactic_eapply H.
      assert_fails (syntactic_apply H).
      syntactic_apply HH.
    Qed.

    Goal forall P eq (H: forall P (Hx:eq I I), P) (HH:eq I I), P.
      intros.
      syntactic_apply H.
      syntactic_apply HH.
    Qed.

    Goal forall R (refl: forall x, R x x), R True True.
      intros.
      assert_succeeds (exact (refl _)).
    Qed.

    Goal forall R (refl: forall x, R x x), R True True.
      intros.
      syntactic_apply refl.
    Qed.

    Goal forall R (refl: forall x, R x x), R True True.
      intros.
      syntactic_apply (refl _).
    Qed.

    Goal forall R (refl: forall x, R x x), R True True.
      intros.
      syntactic_eapply (refl _).
    Qed.

    Goal forall R (refl: forall x, R x x), R True True.
      intros.
      evarconv_eapply refl.
    Qed.

    Goal forall R (refl: forall x, R x x), R True True.
      intros.
      evarconv_apply (refl _).
    Qed.

    Goal forall R (refl: forall x, R x x), R True True.
      intros.
      evarconv_apply refl.
    Qed.

    Goal forall P eq (H: forall (x:True) (Hx:eq x x), P) (HH:eq I I), P.
      intros.
      assert_fails (evarconv_apply H).
      evarconv_eapply H.
      evarconv_eapply HH.
    Qed.
  End WithAnd.
End _test.