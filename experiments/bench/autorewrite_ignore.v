Definition ignore (n:nat) := tt.
Lemma ignore_S x : ignore (S x) = ignore x. exact eq_refl. Qed.
Hint Rewrite ignore_S : ignore.

Goal ignore  125 = tt. Time autorewrite with ignore. exact eq_refl. Time Qed.
Goal ignore  250 = tt. Time autorewrite with ignore. exact eq_refl. Time Qed.
Goal ignore  500 = tt. Time autorewrite with ignore. exact eq_refl. Time Qed.
Goal ignore 1000 = tt. Time autorewrite with ignore. exact eq_refl. Time Qed.

(* same as rewrite_ignore.v *)
(* Finished transaction in 0.105 secs (0.058u,0.046s) (successful)
Finished transaction in 0.067 secs (0.055u,0.012s) (successful)
Finished transaction in 0.2 secs (0.199u,0.s) (successful)
Finished transaction in 0.172 secs (0.171u,0.s) (successful)
Finished transaction in 0.748 secs (0.741u,0.002s) (successful)
Finished transaction in 0.683 secs (0.677u,0.003s) (successful)
Finished transaction in 2.946 secs (2.928u,0.003s) (successful)
Finished transaction in 2.67 secs (2.659u,0.s) (successful)
coqc experiments/bench/autorewrite_ignore.v  7.92s user 0.10s system 99% cpu 8.058 total *)
