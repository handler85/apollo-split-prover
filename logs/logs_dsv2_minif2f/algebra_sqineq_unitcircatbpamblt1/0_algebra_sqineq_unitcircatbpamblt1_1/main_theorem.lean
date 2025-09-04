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

lemma algebra_sqineq_unitcircatbpamblt1_1
  (a b : ℝ)
  (h₀ : a ^ (2 : ℕ) + b ^ (2 : ℕ) = (1 : ℝ)) :
  a * b + (a - b) ≤ (1 : ℝ) := by
  have h_main : a * b + (a - b) ≤ (1 : ℝ) := by
    have h₁ : a ^ 2 + b ^ 2 = 1 := by
      simpa [pow_two] using h₀
    have h₂ : a ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg b]
    have h₃ : b ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg a]
    have h₄ : a ≤ 1 := by
      nlinarith
    have h₅ : b ≥ -1 := by
      nlinarith [sq_nonneg (b + 1)]
    have h₆ : a ≥ -1 := by
      nlinarith [sq_nonneg (a + 1)]
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b + 1), sq_nonneg (a + b), sq_nonneg (a - b),
      sq_nonneg (a + 1), sq_nonneg (b - 1), mul_self_nonneg (a - b + 1),
      mul_self_nonneg (a + b - 1), mul_self_nonneg (a + b + 1), mul_self_nonneg (a - b - 1)]
  exact h_main
