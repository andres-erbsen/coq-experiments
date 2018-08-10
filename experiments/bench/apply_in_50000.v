Require Import Coq.Init.Prelude.

Lemma H : True -> True. trivial. Qed.

Goal True -> True.
  intros G.
  Time (do 50000 apply H in G); exact G.
Time Qed.
(*
Finished transaction in 2.042 secs (1.891u,0.142s) (successful)
Finished transaction in 0.218 secs (0.217u,0.s) (successful)
*)
