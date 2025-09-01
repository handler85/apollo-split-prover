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
lemma algebra_sqineq_unitcircatbpabsamblt1_1
  (a b : ℝ)
  (h₀ : a ^ (2 : ℕ) + b ^ (2 : ℕ) = (1 : ℝ))
  (h : b ≤ a) :
  a + (a * b - b) ≤ (1 : ℝ) := by
  have h_main : a + (a * b - b) ≤ (1 : ℝ) := by
    have h₁ : a ^ 2 + b ^ 2 = 1 := by
      norm_cast at h₀ ⊢
      <;>
      (try ring_nf at h₀ ⊢ <;> simp_all) <;>
      nlinarith
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (a + b), sq_nonneg (a - b),
      sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), mul_self_nonneg (a - b),
      mul_self_nonneg (a + b - 1), mul_self_nonneg (a + b + 1),
      mul_self_nonneg (a * b - 1 / 4)]
  
  exact h_main
