import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
set_option pp.instanceTypes true
set_option pp.numericTypes true
set_option pp.coercions.types true
set_option pp.letVarTypes true
set_option pp.structureInstanceTypes true
set_option pp.instanceTypes true
set_option pp.mvars.withType true
set_option pp.coercions true
set_option pp.funBinderTypes true
set_option pp.piBinderTypes true

lemma amc12a_2020_p7_6
  (a : ℕ → ℕ)
  (ha0 : a (0 : ℕ) = (1 : ℕ))
  (ha1 : a (1 : ℕ) = (2 : ℕ))
  (ha2 : a (2 : ℕ) = (3 : ℕ))
  (ha3 : a (3 : ℕ) = (4 : ℕ))
  (ha4 : a (4 : ℕ) = (5 : ℕ))
  (ha5 : a (5 : ℕ) = (6 : ℕ))
  (ha6 : a (6 : ℕ) = (7 : ℕ)) :
  ∑ x ∈ Finset.range (7 : ℕ), a x ^ (2 : ℕ) * (6 : ℕ) = (840 : ℕ) := by
  have h_main : ∑ x ∈ Finset.range (7 : ℕ), a x ^ (2 : ℕ) * (6 : ℕ) = 840 := by
    simp [Finset.sum_range_succ, ha0, ha1, ha2, ha3, ha4, ha5, ha6, pow_two]
    <;> norm_num
    <;> rfl
  exact h_main
