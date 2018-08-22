Require Import Coq.Init.Prelude.

Tactic Notation "texact" tactic(x) := exact x.
Notation "'subst!' y 'for' x 'in' f" := (match y with x => f end) (at level 10, f at level 200).
Ltac delta1 x :=
  let y := eval unfold x in x in y.
Global Notation "'delta1!' x" := (ltac:(texact (delta1 x))) (only parsing, at level 10).
Ltac delta1_or_id x :=
  match constr:(Set) with
  | _ => let y := eval unfold x in x in y
  | _ => x
  end.

Ltac bind_subterms_rec e k :=
  let t := type of e in
  lazymatch e with
  | ?f ?x =>
    bind_subterms_rec f ltac:(fun f =>
    bind_subterms_rec x ltac:(fun x =>
    let fx := fresh in
    constr:(let fx : t := f x in
    ltac:(texact (k fx)))))
  | let origx : ?tx := ?ex in ?eC =>
    bind_subterms_rec ex ltac:(fun ex =>
    let ex := delta1_or_id ex in
    let freshx := fresh in
    constr:(let freshx : tx := ex in
    ltac:(let C := constr:(subst! freshx for origx in eC) in
    texact (bind_subterms_rec C k))))
  | fun origx : ?tx => ?eC =>
    k constr:(fun x : tx =>
      ltac:(let C := constr:(subst! x for origx in eC) in
      bind_subterms_rec C ltac:(fun C =>
      let C := delta1_or_id C in
      exact C)))
  | _ => k e
  end.
Ltac bind_subterms e :=
  bind_subterms_rec e ltac:(fun x => let x := delta1_or_id x in x).

Goal exists x, x = 10.
  assert (n : nat) by exact O.

  let e := constr:(O+1) in
  let e' := bind_subterms_rec e ltac:(fun z => z) in
  (assert (e = e') by exact eq_refl) || pose e'.

  let e := constr:(let x := 1 in let y := 2 in x+y) in
  let e' := bind_subterms_rec e ltac:(fun z => z) in
  (assert (e = e') by exact eq_refl) || pose e'.

  let e := constr:((fun A:nat => A) 7) in
  let e' := bind_subterms_rec e ltac:(fun z => z) in
  (assert (e = e') by exact eq_refl) || pose e'.
