Require Import Coq.Init.Prelude.

Ltac poses n :=
  lazymatch n with
  | S ?n =>
    poses n;
    lazymatch goal with n := _ |- _ => pose (S n) end
  | _ =>
    pose O
  end.

Goal True. Time poses 125. Abort.
Goal True. Time poses 250. Abort.
Goal True. Time poses 500. Abort.
Goal True. Time poses 1000. Abort.
Goal True. Time poses 2000. Abort.
Goal True. Time poses 4000. Abort.
(*
Finished transaction in 0.019 secs (0.015u,0.004s) (successful)
Finished transaction in 0.06 secs (0.037u,0.022s) (successful)
Finished transaction in 0.194 secs (0.163u,0.029s) (successful)
Finished transaction in 0.666 secs (0.661u,0.002s) (successful)
Finished transaction in 3.133 secs (3.068u,0.053s) (successful)
Finished transaction in 15.478 secs (15.292u,0.126s) (successful)
*)
