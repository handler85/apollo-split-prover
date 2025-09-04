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

lemma algebra_sqineq_at2malt1_1
  (a : ℝ)
  (h₁ : a * ((2 : ℝ) - a) = (2 : ℝ) * a - a ^ (2 : ℕ)) :
  (2 : ℝ) * a ≤ (1 : ℝ) + a ^ (2 : ℕ) := by
  have h_main : (2 : ℝ) * a ≤ (1 : ℝ) + a ^ (2 : ℕ) := by
    norm_num [pow_two] at h₁ ⊢
    nlinarith [sq_nonneg (a - 1)]
  exact h_main
