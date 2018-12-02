Definition ignore (n:nat) := tt.
Lemma ignore_S x : ignore (S x) = ignore x. exact eq_refl. Qed.
Create HintDb ignore.
Hint Rewrite ignore_S : ignore.

Goal ignore  125 = tt. Time autorewrite with ignore. exact eq_refl. Time Qed.
Goal ignore  250 = tt. Time autorewrite with ignore. exact eq_refl. Time Qed.
Goal ignore  500 = tt. Time autorewrite with ignore. exact eq_refl. Time Qed.
Goal ignore 1000 = tt. Time autorewrite with ignore. exact eq_refl. Time Qed.

(* same as rewrite_ignore.v *)
(* Finished transaction in 0.106 secs (0.078u,0.026s) (successful)
Finished transaction in 0.067 secs (0.051u,0.016s) (successful)
Finished transaction in 0.2 secs (0.199u,0.s) (successful)
Finished transaction in 0.172 secs (0.17u,0.s) (successful)
Finished transaction in 0.743 secs (0.733u,0.006s) (successful)
Finished transaction in 0.669 secs (0.663u,0.003s) (successful)
Finished transaction in 2.938 secs (2.904u,0.019s) (successful)
Finished transaction in 2.659 secs (2.648u,0.s) (successful) *)