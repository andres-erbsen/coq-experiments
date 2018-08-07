open nat
definition exn : nat → Prop
| exn 0     := true
| exn (n+1) := exists x : true, exn n


lemma exn_1000 : exn 1000 :=
begin
  repeat (constructor)
end