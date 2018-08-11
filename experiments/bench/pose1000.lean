open tactic

lemma test : true :=
begin
  iterate_exactly 1000 (do pose (`_) none `(trivial), skip),
  exact trivial
end
-- 0.61user 0.04system 0:00.65elapsed 99%CPU (0avgtext+0avgdata 96756maxresident)k
