Require Import Coq.Init.Prelude Coq.ZArith.ZArith. Local Open Scope Z_scope.

Definition step (n : Z) :=
  if Z.eqb n 1 then None else
  if Z.even n
  then Some (Z.div2 n)
  else Some (3*n + 1).

Ltac collatz :=
  intros;
  repeat
  lazymatch goal with
  | H: _ = ?RHS |- _ =>
    lazymatch RHS with
    | Some ?n =>
    let H := lazymatch goal with H:n = _ |- _ => H end in
    first
      [
        let n' := open_constr:(_) in
        let n'' := fresh "n" in
        let Hn'' := fresh "H" n'' in
        refine (let n'' : Z := n' in let Hn'' : n'' = n' := eq_refl in _); clearbody Hn'';
        eassert (step n = Some n'') by (rewrite H; cbv; refine eq_refl); clearbody n''
      | exists n; rewrite H; refine eq_refl ]
    end
  end.

(* 350 steps *)
Goal forall n, n = 77031 -> Some n = Some n -> exists n, step n = None.
Time collatz. Time Qed.
(*
Finished transaction in 7.02 secs (6.882u,0.102s) (successful)
Finished transaction in 0.119 secs (0.119u,0.s) (successful)
*)

(* 685 steps *)
Goal forall n, n = 8400511 -> Some n = Some n -> exists n, step n = None.
Time collatz. Time Qed.
(*
Finished transaction in 37.63 secs (37.103u,0.351s) (successful)
Finished transaction in 0.286 secs (0.282u,0.003s) (successful)
*)