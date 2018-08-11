open tactic

lemma test : true :=
begin
  iterate_exactly 10000 (do pose (`_) none `(trivial), skip),
  exact trivial
end
-- 1.15user 0.07system 0:01.21elapsed 100%CPU (0avgtext+0avgdata 149704maxresident)k
