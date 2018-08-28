Require Import Coq.Init.Tactics.

Definition id_True (x : True) : True := x.

Goal True.  Time do 1000 simple refine (id_True _). exact I. Time Optimize Proof. Time Qed.
(* Finished transaction in 0.034 secs (0.013u,0.02s) (successful)
   Evars: 2001 -> 0
   Finished transaction in 0. secs (0.u,0.s) (successful)
   Finished transaction in 0.002 secs (0.002u,0.s) (successful) *)
Goal True.  Time do 10000 simple refine (id_True _). exact I. Time Optimize Proof. Time Qed.
(* Finished transaction in 0.284 secs (0.221u,0.062s) (successful)
   Evars: 20001 -> 0
   Finished transaction in 0.005 secs (0.005u,0.s) (successful)
   Finished transaction in 0.015 secs (0.015u,0.s) (successful) *)
Goal True.  Time do 100000 simple refine (id_True _). exact I. Time Optimize Proof. Time Qed.
(* Finished transaction in 2.411 secs (2.324u,0.079s) (successful)
   Evars: 200001 -> 0
   Finished transaction in 0.056 secs (0.056u,0.s) (successful)
   Finished transaction in 0.221 secs (0.197u,0.023s) (successful) *)
Goal True.  Time do 1000000 simple refine (id_True _). exact I. Time Optimize Proof. Time Qed.
(* Finished transaction in 27.145 secs (26.175u,0.84s) (successful)
   Evars: 2000001 -> 0
   Finished transaction in 0.669 secs (0.607u,0.059s) (successful)
   Finished transaction in 5.337 secs (5.254u,0.066s) (successful) *)

(* sh -c 'ulimit -s unlimited ; coqc bench/refine_id.v'  35.18s user 1.30s system 99% cpu 36.639 total *)