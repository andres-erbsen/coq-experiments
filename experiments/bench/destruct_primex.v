Local Set Primitive Projections. Local Unset Printing Primitive Projection Parameters.
Record ex {A} (P:A->Type) : Type := ex_intro { ex_x : A; ex_pf : P ex_x }.
Notation "'exists' x .. y , p" := (ex (fun x => .. (ex (fun y => p)) ..)) : type_scope.
Ltac destruct_primex H :=
  lazymatch type of H with @ex ?A (fun x => ?P) =>
  let Hx := fresh in
  let Hpf := fresh in
  pose (@ex_x A (fun x => P) H) as Hx;
  (* pose (@ex_pf A (fun x => P) H : match Hx with x => P end) as Hpf; *)
  assert (match Hx with x => P end) as Hpf by exact (@ex_pf A (fun x => P) H);
  clearbody Hx; try clear H
  end.

Fixpoint exn (n:nat) : Type :=
  match n with O => False | S n => exists tt:unit, exn n end.

Goal exn 125 -> False. intro H. cbv in H.
  Time (repeat match goal with H:exists _, _ |-_=> destruct_primex H end; assumption).
Time Qed.
(* Finished transaction in 0.328 secs (0.237u,0.089s) (successful) *)
(* Finished transaction in 0.068 secs (0.064u,0.002s) (successful) *)

Goal exn 250 -> False. intro H. cbv in H.
  idtac "".
  Time (repeat match goal with H:exists _, _ |-_=> destruct_primex H end; assumption).
Time Qed.
(* Finished transaction in 1.196 secs (1.179u,0.01s) (successful) *)
(* Finished transaction in 0.253 secs (0.252u,0.s) (successful) *)

Goal exn 500 -> False. intro H. cbv in H.
  idtac "".
  Time (repeat match goal with H:exists _, _ |-_=> destruct_primex H end; assumption).
Time Qed.
(* Finished transaction in 7.028 secs (6.967u,0.026s) (successful) *)
(* Finished transaction in 1.011 secs (1.004u,0.s) (successful) *)

Goal exn 1000 -> False. intro H. cbv in H.
  idtac "".
  Time (repeat match goal with H:exists _, _ |-_=> destruct_primex H end; assumption).
Time Qed.
(* Finished transaction in 46.185 secs (45.762u,0.205s) (successful) *)
(* Finished transaction in 3.957 secs (3.931u,0.s) (successful) *)

Goal exn 2000 -> False. intro H. cbv in H.
  idtac "".
  Time (repeat match goal with H:exists _, _ |-_=> destruct_primex H end; assumption).
Time Qed.
(* Finished transaction in 331.19 secs (329.098u,0.622s) (successful) *)
(* Finished transaction in 16.489 secs (16.377u,0.009s) (successful) *)

(* coqc destruct_primex.v  470.79s user 1.21s system 99% cpu 7:54.14 total *)
(* 3GB RAM *)
