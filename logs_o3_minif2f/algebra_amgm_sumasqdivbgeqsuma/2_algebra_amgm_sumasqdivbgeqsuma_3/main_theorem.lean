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

lemma algebra_amgm_sumasqdivbgeqsuma_3
  (a b c d : ℝ)
  (h₀ : (0 : ℝ) < a ∧ (0 : ℝ) < b ∧ (0 : ℝ) < c ∧ (0 : ℝ) < d)
  (h2 : b * (2 : ℝ) ≤ c + b ^ (2 : ℕ) * c⁻¹)
  (h1 : a * (2 : ℝ) ≤ b + a ^ (2 : ℕ) * b⁻¹) :
  c * (2 : ℝ) ≤ c ^ (2 : ℕ) * d⁻¹ + d := by
  have h_d_pos : d > 0 := by linarith [h₀.1, h₀.2.1, h₀.2.2.1, h₀.2.2.2]
  have h_main : c * (2 : ℝ) ≤ c ^ (2 : ℕ) * d⁻¹ + d := by
    have h₃ : 0 < c := by linarith [h₀.2.2.1]
    have h₄ : 0 < d := by linarith [h₀.2.2.2]
    have h₅ : 0 < c * d := by positivity
    have h₆ : 0 < c * d * d := by positivity
    field_simp [h₃.ne', h₄.ne']
    rw [le_div_iff (by positivity)]
    nlinarith [sq_nonneg (c - d), sq_nonneg (c + d), sq_nonneg (c - 2 * d),
      sq_nonneg (c + 2 * d), mul_pos h₃ h₄, mul_pos (mul_pos h₃ h₄) h₄,
      mul_pos (mul_pos h₃ h₄) h₃]
  exact h_main
