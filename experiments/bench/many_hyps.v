Require Import Coq.Init.Prelude.

Goal True. Time (do 125 pose proof I). exact I. Qed.
(* Finished transaction in 0.009 secs (0.009u,0.s) (successful) *)
Goal True. Time (do 250 pose proof I). exact I. Qed.
(* Finished transaction in 0.027 secs (0.024u,0.003s) (successful) *)
Goal True. Time (do 500 pose proof I). exact I. Qed.
(* Finished transaction in 0.117 secs (0.106u,0.01s) (successful) *)
Goal True. Time (do 1000 pose proof I). exact I. Qed.
(* Finished transaction in 0.43 secs (0.409u,0.02s) (successful) *)
Goal True. Time (do 2000 pose proof I). exact I. Qed.
(* Finished transaction in 1.771 secs (1.714u,0.049s) (successful) *)
Goal True. Time (do 4000 pose proof I). exact I. Qed.
(* Finished transaction in 8.554 secs (8.31u,0.195s) (successful) *)

(* coqc many_hyps.v  176.96s user 0.66s system 99% cpu 2:58.12 total *)
