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

lemma algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3_3
  (a b c : ℝ)
  (h₀ : a ≤ b ∧ b ≤ c)
  (h₁ : a + b + c = (2 : ℝ))
  (disc : a ^ (2 : ℕ) * (3 : ℝ) ≤ a * (4 : ℝ))
  (bc_expr : b * c = (1 : ℝ) - a * (2 : ℝ) + a ^ (2 : ℕ))
  (h₂ : (1 : ℝ) - a * (2 : ℝ) + a * b + a * c + a ^ (2 : ℕ) = (1 : ℝ)) :
  (0 : ℝ) ≤ a := by
  have h_main : 0 ≤ a := by
    by_contra h
    have h₃ : a < 0 := by linarith
    have h₄ : a ^ (2 : ℕ) * (3 : ℝ) ≤ a * (4 : ℝ) := disc
    have h₅ : a ^ 2 * 3 ≤ a * 4 := by
      norm_num at h₄ ⊢
      <;> nlinarith
    nlinarith [sq_nonneg (a - 4 / 3), sq_nonneg (a + 4 / 3), sq_nonneg (a - 2), sq_nonneg (a + 2)]
  exact h_main
