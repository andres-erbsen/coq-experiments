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
  change x with (nth_default 0 0 vars');
  change vars with (skipn 1 vars');
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
Finished transaction in 0.104 secs (0.046u,0.057s) (successful)
Evars: 2505 -> 1
Finished transaction in 0.003 secs (0.003u,0.s) (successful)

Finished transaction in 0.182 secs (0.156u,0.024s) (successful)
Evars: 5005 -> 1
Finished transaction in 0.008 secs (0.008u,0.s) (successful)

Finished transaction in 0.426 secs (0.425u,0.s) (successful)
Evars: 10005 -> 1
Finished transaction in 0.007 secs (0.007u,0.s) (successful)

Finished transaction in 1.433 secs (1.415u,0.009s) (successful)
Evars: 20005 -> 1
Finished transaction in 0.015 secs (0.014u,0.s) (successful)

Finished transaction in 5.158 secs (5.126u,0.012s) (successful)
Evars: 40005 -> 1
Finished transaction in 0.025 secs (0.025u,0.s) (successful)
*)
