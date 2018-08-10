Require Import Coq.Init.Prelude.

Lemma H : True -> True. trivial. Qed.

Goal True -> True.
  intros G.
  Time (do 100000 apply H in G); exact G.
Time Qed.
(*
Finished transaction in 4.167 secs (3.906u,0.242s) (successful)
Finished transaction in 0.4 secs (0.389u,0.01s) (successful)
*)
