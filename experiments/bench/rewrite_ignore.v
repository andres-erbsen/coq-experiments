Definition ignore (n:nat) := tt.
Lemma ignore_S x : ignore (S x) = ignore x. exact eq_refl. Qed.

Goal ignore  125 = tt. Time rewrite !ignore_S. exact eq_refl. Time Qed.
(* Finished transaction in 0.108 secs (0.039u,0.068s) (successful) *)
(* Finished transaction in 0.066 secs (0.05u,0.016s) (successful) *)
Goal ignore  250 = tt. Time rewrite !ignore_S. exact eq_refl. Time Qed.
(* Finished transaction in 0.206 secs (0.204u,0.s) (successful) *)
(* Finished transaction in 0.172 secs (0.171u,0.s) (successful) *)
Goal ignore  500 = tt. Time rewrite !ignore_S. exact eq_refl. Time Qed.
(* Finished transaction in 0.769 secs (0.764u,0.001s) (successful) *)
(* Finished transaction in 0.686 secs (0.677u,0.006s) (successful) *)
Goal ignore 1000 = tt. Time rewrite !ignore_S. exact eq_refl. Time Qed.
(* Finished transaction in 3.011 secs (2.986u,0.009s) (successful) *)
(* Finished transaction in 2.674 secs (2.663u,0.s) (successful) *)

(* coqc experiments/bench/rewrite_ignore.v  7.99s user 0.14s system 99% cpu 8.168 total *)