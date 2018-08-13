Goal True. Time do 250 let x := open_constr:(_:unit) in pose x. Time Optimize Proof. Abort. Optimize Heap.
(* Finished transaction in 0.085 secs (0.062u,0.022s) (successful) *)
(* Evars: 751 -> 251 Finished transaction in 0.098 secs (0.067u,0.03s) (successful) *)
Goal True. Time do 500 let x := open_constr:(_:unit) in pose x. Time Optimize Proof. Abort. Optimize Heap.
(* Finished transaction in 0.3 secs (0.286u,0.013s) (successful) *)
(* Evars: 1501 -> 501 Finished transaction in 0.509 secs (0.505u,0.003s) (successful) *)
Goal True. Time do 1000 let x := open_constr:(_:unit) in pose x. Time Optimize Proof. Abort. Optimize Heap.
(* Finished transaction in 1.36 secs (1.327u,0.029s) (successful) *)
(* Evars: 3001 -> 1001 Finished transaction in 4.191 secs (4.172u,0.01s) (successful) *)
Goal True. Time do 2000 let x := open_constr:(_:unit) in pose x. Time Optimize Proof. Abort. Optimize Heap.
(* Finished transaction in 7.053 secs (6.866u,0.139s) (successful) *)
(* Evars: 6001 -> 2001 Finished transaction in 38.897 secs (38.714u,0.029s) (successful) *)
Goal True. Time do 4000 let x := open_constr:(_:unit) in pose x. Time Optimize Proof. Abort. Optimize Heap.
(* Finished transaction in 33.937 secs (33.338u,0.451s) (successful) *)
(* Evars: 12001 -> 4001 Finished transaction in 380.494 secs (379.115u,0.26s) (successful) *)
Goal True. Time do 8000 let x := open_constr:(_:unit) in pose x. Time Optimize Proof. Abort. Optimize Heap.
(* Finished failing transaction in 104.22 secs (102.416u,1.314s) (failure) *)
(* Error: Out of memory. *)

(* TOTAL coqc evar_epose.v  568.57s user 2.59s system 99% cpu 9:33.14 total *)
