Require Import Coq.Init.Prelude Coq.ZArith.ZArith. Local Open Scope Z_scope.

Definition step (n : Z) :=
  if Z.eqb n 1 then None else
  if Z.even n
  then Some (Z.div2 n)
  else Some (3*n + 1).

Ltac collatz :=
  intros;
  subst;
  repeat
  lazymatch goal with
  | H: _ = ?RHS |- _ =>
    lazymatch RHS with
    | Some ?n =>
    first
      [
        let n' := open_constr:(_) in
        eassert (step n = Some n') by (cbv; refine eq_refl)
      | exists n; refine eq_refl ]
    end
  end.

(* 350 steps *)
Goal forall n, n = 77031 -> Some n = Some n -> exists n, step n = None.
Time collatz. Time Qed.
(*
Finished transaction in 1.148 secs (1.143u,0.s) (successful)
Finished transaction in 0.077 secs (0.077u,0.s) (successful)
*)

(* 685 steps *)
Goal forall n, n = 8400511 -> Some n = Some n -> exists n, step n = None.
Time collatz. Time Qed.
(*
Finished transaction in 4.967 secs (4.877u,0.062s) (successful)
Finished transaction in 0.208 secs (0.207u,0.s) (successful)
*)