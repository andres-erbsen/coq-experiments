Require Import BinInt.

Fixpoint skipn (n : nat) ( l :list nat) : list nat :=
  match n with
  | 0 => l
  | S n => match l with
           | nil => nil
           | cons a l => skipn n l
           end
  end.

Definition nth_default d n xs :=
  match skipn n xs with
  | cons x _ => x
  | _ => d
  end.

Ltac cintro vars :=
  let x := fresh in
  intros x;
  pose (vars' := @cons nat x vars);
  change x with (nth_default 0 (Z.to_nat 0) vars');
  repeat match goal with
  |- context[skipn (Z.to_nat ?s) vars] =>
      let s' := eval cbv in (Z.succ s) in
      change (skipn (Z.to_nat s) vars)
        with (skipn (Z.to_nat s') vars')
  end;
  change vars with (skipn (Z.to_nat 1) vars');
  clearbody vars';
  clear x;
  clear vars;
  rename vars' into vars.

Fixpoint foralln n (x : nat) (k : nat -> Prop) :=
  match n with
  | O => k x
  | S n =>
    forall x : nat, foralln n x k
  end.

Goal forall (vars : list nat) (a b c : nat),
   a + b + c = c + b + a.
  intros ?.
  cintro vars.
  cintro vars.
  cintro vars.
Abort.

Goal foralln 250 O (fun _=> True). cbv beta iota delta [foralln].
Proof. pose (vars := @nil nat). Time repeat cintro vars. Time Optimize Proof. exact I. Qed.
Goal foralln 500 O (fun _=> True). cbv beta iota delta [foralln].
Proof. pose (vars := @nil nat). Time repeat cintro vars. Time Optimize Proof. exact I. Qed.
Goal foralln 1000 O (fun _=> True). cbv beta iota delta [foralln].
Proof. pose (vars := @nil nat). Time repeat cintro vars. Time Optimize Proof. exact I. Qed.
Goal foralln 2000 O (fun _=> True). cbv beta iota delta [foralln].
Proof. pose (vars := @nil nat). Time repeat cintro vars. Time Optimize Proof. exact I. Qed.
Goal foralln 4000 O (fun _=> True). cbv beta iota delta [foralln].
Proof. pose (vars := @nil nat). Time repeat cintro vars. Time Optimize Proof. exact I. Qed.
(*
Finished transaction in 0.116 secs (0.085u,0.029s) (successful)
Evars: 2505 -> 1
Finished transaction in 0.001 secs (0.001u,0.s) (successful)

Finished transaction in 0.192 secs (0.188u,0.002s) (successful)
Evars: 5005 -> 1
Finished transaction in 0.003 secs (0.003u,0.s) (successful)

Finished transaction in 0.675 secs (0.67u,0.s) (successful)
Evars: 10005 -> 1
Finished transaction in 0.007 secs (0.007u,0.s) (successful)

Finished transaction in 1.98 secs (1.964u,0.004s) (successful)
Evars: 20005 -> 1
Finished transaction in 0.014 secs (0.014u,0.s) (successful)

Finished transaction in 7.248 secs (7.209u,0.01s) (successful)
Evars: 40005 -> 1
Finished transaction in 0.037 secs (0.037u,0.s) (successful)
*)
