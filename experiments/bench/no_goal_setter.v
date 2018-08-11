Require Import Coq.Init.Prelude.

Inductive good : nat -> Prop :=
| good_O : good O
| good_S n (_:good n) : good (S n).


Goal good 1000.
  Time repeat constructor.
  (* Finished transaction in 1.151 secs (1.074u,0.072s) (successful) *)
Time Optimize Proof.
(* Evars: 2002 -> 0 *)
(* Finished transaction in 0.024 secs (0.023u,0.s) (successful) *)
Time Qed.
(* Finished transaction in 0.898 secs (0.895u,0.s) (successful) *)
  
Goal good 2000.
  Time repeat constructor.
  (* Finished transaction in 4.53 secs (4.422u,0.089s) (successful) *)
Time Optimize Proof.
(* Evars: 4002 -> 0 *)
(* Finished transaction in 0.073 secs (0.072u,0.s) (successful) *)
Time Qed.
(* Finished transaction in 3.704 secs (3.693u,0.s) (successful) *)