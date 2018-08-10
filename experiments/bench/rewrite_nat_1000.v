Require Import Coq.Init.Prelude.

Lemma H : 1000 = id 1000. exact eq_refl. Qed.
Goal exists e, e = 1000.
  eexists.
  Time do 5000 (rewrite H; rewrite <-H).
  reflexivity.
Time Qed.
(*
Finished transaction in 65.496 secs (64.611u,0.52s) (successful)
Finished transaction in 60.687 secs (60.346u,0.033s) (successful)
*)