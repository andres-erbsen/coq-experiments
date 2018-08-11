Require Import Coq.Init.Prelude.

Goal True.
  Time (do 1000 pose proof I).
  (* Finished transaction in 0.402 secs (0.397u,0.003s) (successful) *)
  Time Optimize Proof.
  (* Evars: 2001 -> 1
     Finished transaction in 1.334 secs (1.332u,0.s) (successful) *)
  Time (do 1000 pose proof I).
  (* Finished transaction in 1.219 secs (1.201u,0.013s) (successful) *)
Abort.