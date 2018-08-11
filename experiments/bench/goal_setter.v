Require Import Coq.Init.Prelude.

Inductive good : nat -> Prop :=
| good_O : good O
| good_S n (_:good n) : good (S n).


Goal good 1000.
  Time
  repeat match goal with
  | |- context G[S ?n] =>
    first [is_var n | is_const n | is_constructor n];
      let x := fresh in
      pose (S n) as x;
      let goal := context G [ x ] in
      change goal
  end.
  (* Finished transaction in 31.268 secs (31.073u,0.093s) (successful) *)
  Time repeat constructor.
  (* Finished transaction in 0.448 secs (0.446u,0.s) (successful) *)
Time Optimize Proof.
(* Evars: 5002 -> 0 *)
(* Finished transaction in 6.884 secs (6.875u,0.s) (successful) *)
Time Qed.
(* Finished transaction in 0.036 secs (0.036u,0.s) (successful) *)
  