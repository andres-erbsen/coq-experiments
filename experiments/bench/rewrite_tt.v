Require Import Coq.Init.Prelude.

Lemma H : tt = id tt. exact eq_refl. Qed.
Goal exists e, e = tt.
  eexists.
  Time do 5000 (rewrite H; rewrite <-H).
  reflexivity.
Time Qed.
(*
Finished transaction in 1.087 secs (1.081u,0.s) (successful)
Finished transaction in 0.197 secs (0.196u,0.s) (successful)
*)