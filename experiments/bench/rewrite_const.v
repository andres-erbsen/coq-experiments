Definition ignore (n:nat) := tt.
Lemma ignore_S x : ignore (S x) = ignore x. exact eq_refl. Qed.

Goal ignore 1 = tt. Time do 1000 rewrite ignore_S, <-ignore_S. exact eq_refl. Time Qed.
(* Finished transaction in 0.266 secs (0.265u,0.s) (successful) *)
(* Finished transaction in 0.047 secs (0.046u,0.s) (successful) *)
Goal ignore 1 = tt. Time do 2000 rewrite ignore_S, <-ignore_S. exact eq_refl. Time Qed.
(* Finished transaction in 0.512 secs (0.5u,0.009s) (successful) *)
(* Finished transaction in 0.096 secs (0.096u,0.s) (successful) *)
Goal ignore 1 = tt. Time do 4000 rewrite ignore_S, <-ignore_S. exact eq_refl. Time Qed.
(* Finished transaction in 1.017 secs (0.995u,0.016s) (successful) *)
(* Finished transaction in 0.178 secs (0.171u,0.006s) (successful) *)
Goal ignore 1 = tt. Time do 8000 rewrite ignore_S, <-ignore_S. exact eq_refl. Time Qed.
(* Finished transaction in 2.154 secs (2.139u,0.003s) (successful) *)
(* Finished transaction in 0.368 secs (0.366u,0.s) (successful) *)
Goal ignore 1 = tt. Time do 16000 rewrite ignore_S, <-ignore_S. exact eq_refl. Time Qed.
(* Finished transaction in 3.983 secs (3.963u,0.s) (successful) *)
(* Finished transaction in 0.738 secs (0.735u,0.s) (successful) *)
Goal ignore 1 = tt. Time do 32000 rewrite ignore_S, <-ignore_S. exact eq_refl. Time Qed.
(* Finished transaction in 7.956 secs (7.913u,0.003s) (successful) *)
(* Finished transaction in 1.475 secs (1.466u,0.003s) (successful) *)