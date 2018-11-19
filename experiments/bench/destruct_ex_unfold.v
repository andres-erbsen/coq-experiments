Fixpoint exn (n:nat) :=
  match n with O => False | S n => exists tt:unit, exn n end.

Goal exn 125 -> False. intro H.
  Time (repeat match goal with H:exn _ |-_=> destruct H end; assumption).
Time Qed.
(* Finished transaction in 0.222 secs (0.161u,0.059s) (successful) *)
(* Finished transaction in 0.105 secs (0.105u,0.s) (successful) *)

Goal exn 250 -> False. intro H. idtac "".
  Time (repeat match goal with H:exn _ |-_=> destruct H end; assumption).
Time Qed.
(* Finished transaction in 0.511 secs (0.505u,0.002s) (successful) *)
(* Finished transaction in 0.389 secs (0.387u,0.s) (successful) *)

Goal exn 500 -> False. intro H. idtac "".
  Time (repeat match goal with H:exn _ |-_=> destruct H end; assumption).
Time Qed.
(* Finished transaction in 2.439 secs (2.41u,0.013s) (successful) *)
(* Finished transaction in 1.776 secs (1.766u,0.s) (successful) *)

Goal exn 1000 -> False. intro H. idtac "".
  Time (repeat match goal with H:exn _ |-_=> destruct H end; assumption).
Time Qed.
(* Finished transaction in 8.632 secs (8.509u,0.066s) (successful) *)
(* Finished transaction in 6.266 secs (6.226u,0.003s) (successful) *)

Goal exn 2000 -> False. intro H. idtac "".
  Time (repeat match goal with H:exn _ |-_=> destruct H end; assumption).
Time Qed.
(* Finished transaction in 33.803 secs (33.401u,0.202s) (successful) *)
(* Finished transaction in 26.069 secs (25.866u,0.049s) (successful) *)

(* coqc destruct_ex_unfold.v  121.45s user 0.58s system 99% cpu 2:02.62 total *)
