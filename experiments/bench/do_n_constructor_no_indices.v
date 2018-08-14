Require Import Coq.Init.Prelude.

Goal nat.
  Time do 4000 constructor 2.
  Time constructor.
  Time Optimize Proof.
Time Qed.
(*
Finished transaction in 0.151 secs (0.107u,0.043s) (successful)
Finished transaction in 0. secs (0.u,0.s) (successful)
Evars: 8002 -> 0 Finished transaction in 0.004 secs (0.004u,0.s) (successful)
Finished transaction in 0.015 secs (0.015u,0.s) (successful)
*)

Goal nat.
  Time do 2000 pose proof I.
  Time do 2000 (constructor 2).
  Time constructor.
  Time Optimize Proof.
Time Qed.
(*
Finished transaction in 1.772 secs (1.726u,0.039s) (successful)
Finished transaction in 1.712 secs (1.662u,0.043s) (successful)
Finished transaction in 0. secs (0.u,0.s) (successful)
Evars: 8002 -> 0 Finished transaction in 69.493 secs (69.309u,0.059s) (successful)
Finished transaction in 0.013 secs (0.013u,0.s) (successful)
*)
