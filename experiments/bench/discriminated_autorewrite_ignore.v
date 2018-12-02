Definition ignore (n:nat) := tt.
Lemma ignore_S x : ignore (S x) = ignore x. exact eq_refl. Qed.
Create HintDb ignore discriminated.
Hint Rewrite ignore_S : ignore.

Goal ignore  125 = tt. Time autorewrite with ignore. exact eq_refl. Time Qed.
Goal ignore  250 = tt. Time autorewrite with ignore. exact eq_refl. Time Qed.
Goal ignore  500 = tt. Time autorewrite with ignore. exact eq_refl. Time Qed.
Goal ignore 1000 = tt. Time autorewrite with ignore. exact eq_refl. Time Qed.

(* same as create_rewrite_ignore.v *)
(* Finished transaction in 0.109 secs (0.072u,0.036s) (successful)
Finished transaction in 0.067 secs (0.056u,0.01s) (successful)
Finished transaction in 0.202 secs (0.201u,0.s) (successful)
Finished transaction in 0.171 secs (0.17u,0.s) (successful)
Finished transaction in 0.753 secs (0.742u,0.006s) (successful)
Finished transaction in 0.667 secs (0.664u,0.s) (successful)
Finished transaction in 2.939 secs (2.892u,0.033s) (successful)
Finished transaction in 2.678 secs (2.667u,0.s) (successful) *)