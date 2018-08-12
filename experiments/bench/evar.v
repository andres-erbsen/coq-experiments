Goal True. Time do 250 (let H := fresh in evar (H : unit)). Abort. Optimize Heap.
(* Finished transaction in 0.066 secs (0.042u,0.023s) (successful) *)
Goal True. Time do 500 (let H := fresh in evar (H : unit)). Abort. Optimize Heap.
(* Finished transaction in 0.192 secs (0.192u,0.s) (successful) *)
Goal True. Time do 1000 (let H := fresh in evar (H : unit)). Abort. Optimize Heap.
(* Finished transaction in 0.798 secs (0.779u,0.016s) (successful) *)
Goal True. Time do 2000 (let H := fresh in evar (H : unit)). Abort. Optimize Heap.
(* Finished transaction in 3.692 secs (3.599u,0.083s) (successful) *)
Goal True. Time do 4000 (let H := fresh in evar (H : unit)). Abort. Optimize Heap.
(* Finished transaction in 18.662 secs (18.329u,0.282s) (successful) *)
Goal True. Time do 8000 (let H := fresh in evar (H : unit)). Abort.
(* Finished transaction in 97.144 secs (95.799u,1.073s) (successful) *)

(* 119.28user 1.68system 2:01.31elapsed 99%CPU (0avgtext+0avgdata 4050804maxresident)k
0inputs+0outputs (0major+1272385minor)pagefaults 0swaps *)