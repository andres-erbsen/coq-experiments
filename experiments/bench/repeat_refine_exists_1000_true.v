Require Import Coq.Init.Prelude.

Fixpoint fex (n : nat) : Prop :=
  match n with
  | O => True
  | S n => exists x : True, fex n
  end.

Ltac fex1 :=
  lazymatch goal with
  | |- fex (S ?n) =>
    change (exists x : True,  fex n);
    refine (ex_intro (fun _ => fex n) I _)
  end.

Goal fex 1000.
  Time repeat (lazymatch goal with
               | |- fex (S ?n) =>
                   refine (ex_intro (fun _ => fex n) I _)
               | |- fex 0 =>
                   exact I
               end).
Time Qed.
(*
Finished transaction in 1.751 secs (1.742u,0.s) (successful)
Finished transaction in 2.907 secs (2.883u,0.013s) (successful)
*)