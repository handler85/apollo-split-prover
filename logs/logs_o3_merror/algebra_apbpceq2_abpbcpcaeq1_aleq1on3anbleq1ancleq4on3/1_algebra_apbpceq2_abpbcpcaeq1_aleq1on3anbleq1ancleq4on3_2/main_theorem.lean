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

lemma algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3_2
  (a b c : ℝ)
  (h₀ : a ≤ b ∧ b ≤ c)
  (h₁ : a + b + c = (2 : ℝ))
  (bc_expr : b * c = (1 : ℝ) - a * (2 : ℝ) + a ^ (2 : ℕ))
  (h₂ : (1 : ℝ) - a * (2 : ℝ) + a * b + a * c + a ^ (2 : ℕ) = (1 : ℝ)) :
  a ^ (2 : ℕ) * (3 : ℝ) ≤ a * (4 : ℝ) := by
  have h_main : a ^ (2 : ℕ) * (3 : ℝ) ≤ a * (4 : ℝ) := by
    have h₃ : a ≤ 1 / 2 := by
      nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (b - a), sq_nonneg (c - b),
        sq_nonneg (b - 1 / 2), sq_nonneg (c - 1 / 2)]
    have h₄ : a ≤ 4 / 3 := by
      nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (b - a), sq_nonneg (c - b),
        sq_nonneg (b - 1 / 2), sq_nonneg (c - 1 / 2)]
    have h₅ : a ^ (2 : ℕ) * (3 : ℝ) ≤ a * (4 : ℝ) := by
      have h₆ : a ^ 2 * 3 ≤ a * 4 := by
        nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (a - 4 / 3),
          sq_nonneg (a - 1), sq_nonneg (a + 1)]
      norm_num at h₆ ⊢
      <;> nlinarith
    exact h₅
  exact h_main
