Require Import Coq.Init.Prelude.

Goal True.
  Time (do 10000 (pose proof I as H; clear H)).
  (* Finished transaction in 0.494 secs (0.465u,0.026s) (successful) *)
  Time (do 20000 (pose proof I as H; clear H)).
  (* Finished transaction in 1.02 secs (0.961u,0.046s) (successful) *)
  Time (do 40000 (pose proof I as H; clear H)).
  (* Finished transaction in 2.14 secs (2.027u,0.083s) (successful) *)
  Time (do 80000 (pose proof I as H; clear H)).
  (* Finished transaction in 4.261 secs (4.246u,0.s) (successful) *)
  exact I.
Qed.