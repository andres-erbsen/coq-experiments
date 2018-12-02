Require Import Coq.Init.Prelude.

Goal True.
  Time (pose proof I as H; do 500 (pose proof (id H) as G; clear H; pose proof (id G) as H; clear G); clear H).
  (* Finished transaction in 0.089 secs (0.046u,0.042s) (successful) *)
  Time (pose proof I as H; do 1000 (pose proof (id H) as G; clear H; pose proof (id G) as H; clear G); clear H).
  (* Finished transaction in 0.164 secs (0.123u,0.039s) (successful) *)
  Time (pose proof I as H; do 2000 (pose proof (id H) as G; clear H; pose proof (id G) as H; clear G); clear H).
  (* Finished transaction in 0.256 secs (0.245u,0.009s) (successful) *)
  Time (pose proof I as H; do 4000 (pose proof (id H) as G; clear H; pose proof (id G) as H; clear G); clear H).
  (* Finished transaction in 0.486 secs (0.452u,0.032s) (successful) *)
  Time (pose proof I as H; do 8000 (pose proof (id H) as G; clear H; pose proof (id G) as H; clear G); clear H).
  (* Finished transaction in 1.096 secs (1.032u,0.059s) (successful) *)
  exact I.
Qed.