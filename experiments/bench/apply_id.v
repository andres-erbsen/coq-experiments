Require Import Coq.Init.Prelude.

Goal True.
  Time do 1000000 (apply id).
  Time exact I.
  Time Optimize Proof.
Time Qed.
(*
Finished transaction in 37.501 secs (36.029u,1.162s) (successful)
Finished transaction in 0. secs (0.u,0.s) (successful)
Evars: 1000001 -> 0

Finished transaction in 0.636 secs (0.597u,0.036s) (successful)
Finished transaction in 6.162 secs (5.995u,0.142s) (successful)
coqc apply_id.v  43.15s user 1.52s system 99% cpu 45.008 total
*)
