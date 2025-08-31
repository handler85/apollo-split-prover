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

lemma algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3_4
  (a b c : ℝ)
  (h₀ : a ≤ b ∧ b ≤ c)
  (h₁ : a + b + c = (2 : ℝ))
  (a_nonneg : (0 : ℝ) ≤ a)
  (disc : a ^ (2 : ℕ) * (3 : ℝ) ≤ a * (4 : ℝ))
  (bc_expr : b * c = (1 : ℝ) - a * (2 : ℝ) + a ^ (2 : ℕ))
  (h₂ : (1 : ℝ) - a * (2 : ℝ) + a * b + a * c + a ^ (2 : ℕ) = (1 : ℝ)) :
  a ≤ (1 / 3 : ℝ) := by
  have h_main : a ≤ (1 / 3 : ℝ) := by
    norm_num [pow_two, pow_three] at disc h₂ bc_expr ⊢
    nlinarith [sq_nonneg (a - 1 / 3), sq_nonneg (b - 1 / 3), sq_nonneg (c - 1 / 3),
      mul_nonneg a_nonneg (sub_nonneg.mpr h₀.1), mul_nonneg a_nonneg (sub_nonneg.mpr h₀.2),
      mul_nonneg a_nonneg (sub_nonneg.mpr h₀.1), mul_nonneg a_nonneg (sub_nonneg.mpr h₀.2),
      mul_nonneg (sub_nonneg.mpr h₀.1) (sub_nonneg.mpr h₀.2),
      mul_nonneg (sub_nonneg.mpr h₀.1) a_nonneg, mul_nonneg (sub_nonneg.mpr h₀.2) a_nonneg]
  
  exact h_main
