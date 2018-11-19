Fixpoint exn (n:nat) :=
  match n with O => False | S n => exists tt:unit, exn n end.

Goal exn 125 -> False. intro H. cbv in H.
  Time (repeat match goal with H:exists _, _ |-_=> destruct H end; assumption).
Time Qed.
(* Finished transaction in 0.186 secs (0.105u,0.079s) (successful) *)
(* Finished transaction in 0.115 secs (0.114u,0.s) (successful) *)

Goal exn 250 -> False. intro H. cbv in H.
  idtac "".
  Time (repeat match goal with H:exists _, _ |-_=> destruct H end; assumption).
Time Qed.
(* Finished transaction in 0.454 secs (0.451u,0.s) (successful) *)
(* Finished transaction in 0.448 secs (0.444u,0.s) (successful) *)

Goal exn 500 -> False. intro H. cbv in H.
  idtac "".
  Time (repeat match goal with H:exists _, _ |-_=> destruct H end; assumption).
Time Qed.
(* Finished transaction in 1.935 secs (1.898u,0.022s) (successful) *)
(* Finished transaction in 1.844 secs (1.824u,0.006s) (successful) *)

Goal exn 1000 -> False. intro H. cbv in H.
  idtac "".
  Time (repeat match goal with H:exists _, _ |-_=> destruct H end; assumption).
Time Qed.
(* Finished transaction in 7.444 secs (7.314u,0.079s) (successful) *)
(* Finished transaction in 7.449 secs (7.404u,0.s) (successful) *)

Goal exn 2000 -> False. intro H. cbv in H.
  idtac "".
  Time (repeat match goal with H:exists _, _ |-_=> destruct H end; assumption).
Time Qed.
(* Finished transaction in 30.733 secs (30.302u,0.238s) (successful) *)
(* Finished transaction in 30.184 secs (29.991u,0.026s) (successful) *)

(* coqc destruct_ex.v  125.62s user 0.66s system 99% cpu 2:06.88 total *)
