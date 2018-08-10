Require Import Coq.Init.Prelude.

Fixpoint deep (n : nat) : Set :=
  match n with
  | O => unit
  | S n => option (deep n)
  end.

Goal deep 300 * deep 300 * deep 300 * deep 300 * deep 300 * deep 300 * deep 300 * deep 300 * deep 300 * deep 300.
  Time
  assert (H0: deep 300) by (clear; abstract (repeat constructor));
  assert (H1: deep 300) by (clear; abstract (repeat constructor));
  assert (H2: deep 300) by (clear; abstract (repeat constructor));
  assert (H3: deep 300) by (clear; abstract (repeat constructor));
  assert (H4: deep 300) by (clear; abstract (repeat constructor));
  assert (H5: deep 300) by (clear; abstract (repeat constructor));
  assert (H6: deep 300) by (clear; abstract (repeat constructor));
  assert (H7: deep 300) by (clear; abstract (repeat constructor));
  assert (H8: deep 300) by (clear; abstract (repeat constructor));
  assert (H9: deep 300) by (clear; abstract (repeat constructor)).
  (* Finished transaction in 2.603 secs (2.587u,0.s) (successful) *)
  exact (H0, H1, H2, H3, H4, H5, H6, H7, H8, H9).
  (* Set Printing Implicit. Show Proof. *)
  Time Check
  (let H0 := Unnamed_thm_subproof in
   let H1 := Unnamed_thm_subproof0 in
   let H2 := Unnamed_thm_subproof1 in
   let H3 := Unnamed_thm_subproof2 in
   let H4 := Unnamed_thm_subproof3 in
   let H5 := Unnamed_thm_subproof4 in
   let H6 := Unnamed_thm_subproof5 in
   let H7 := Unnamed_thm_subproof6 in
   let H8 := Unnamed_thm_subproof7 in
   let H9 := Unnamed_thm_subproof8 in
   (H0, H1, H2, H3, H4, H5, H6, H7, H8, H9))
  : deep 300 * deep 300 * deep 300 * deep 300 * deep 300 * deep 300 * deep 300 * deep 300 * deep 300 * deep 300.
  (* Finished transaction in 0.141 secs (0.141u,0.s) (successful) *)
Time Qed.
(* Finished transaction in 0.637 secs (0.634u,0.s) (successful) *)

(* 
Set Printing Implicit.
Set Printing Depth 999999.
Print Unnamed_thm.
( ...
         (fun Top_Unnamed_thm_subproof8 : deep 300 =>
          let H0 := Top_Unnamed_thm_subproof in
          let H1 := Top_Unnamed_thm_subproof0 in
          let H2 := Top_Unnamed_thm_subproof1 in
          let H3 := Top_Unnamed_thm_subproof2 in
          let H4 := Top_Unnamed_thm_subproof3 in
          let H5 := Top_Unnamed_thm_subproof4 in
          let H6 := Top_Unnamed_thm_subproof5 in
          let H7 := Top_Unnamed_thm_subproof6 in
          let H8 := Top_Unnamed_thm_subproof7 in
          let H9 := Top_Unnamed_thm_subproof8 in (H0, H1, H2, H3, H4, H5, H6, H7, H8, H9))

           (@Some (deep 299)
              (@Some (deep 298)
                 (@Some (deep 297)
                    (@Some (deep 296)
                       (@Some (deep 295)
                          (@Some (deep 294) ... ) ... *)


Goal deep 300 * deep 300 * deep 300 * deep 300 * deep 300 * deep 300 * deep 300 * deep 300 * deep 300 * deep 300.
  Time
  assert (H0: deep 300) by (clear; (repeat constructor));
  assert (H1: deep 300) by (clear; (repeat constructor));
  assert (H2: deep 300) by (clear; (repeat constructor));
  assert (H3: deep 300) by (clear; (repeat constructor));
  assert (H4: deep 300) by (clear; (repeat constructor));
  assert (H5: deep 300) by (clear; (repeat constructor));
  assert (H6: deep 300) by (clear; (repeat constructor));
  assert (H7: deep 300) by (clear; (repeat constructor));
  assert (H8: deep 300) by (clear; (repeat constructor));
  assert (H9: deep 300) by (clear; (repeat constructor)).
  (* Finished transaction in 1.146 secs (1.133u,0.006s) (successful) *)
  exact (H0, H1, H2, H3, H4, H5, H6, H7, H8, H9).
Time Qed.
(* Finished transaction in 1.466 secs (1.454u,0.003s) (successful) *)