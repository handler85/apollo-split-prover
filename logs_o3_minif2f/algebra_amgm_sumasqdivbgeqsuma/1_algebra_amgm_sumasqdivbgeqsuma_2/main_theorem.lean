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

lemma algebra_amgm_sumasqdivbgeqsuma_2
  (a b c d : ℝ)
  (h₀ : (0 : ℝ) < a ∧ (0 : ℝ) < b ∧ (0 : ℝ) < c ∧ (0 : ℝ) < d)
  (h1 : a * (2 : ℝ) ≤ b + a ^ (2 : ℕ) * b⁻¹) :
  b * (2 : ℝ) ≤ b ^ (2 : ℕ) * c⁻¹ + c := by
  have h_main : b * (2 : ℝ) ≤ b ^ (2 : ℕ) * c⁻¹ + c := by
    have h2 : 0 < b := by linarith
    have h3 : 0 < c := by linarith
    have h4 : 0 < b ^ (2 : ℕ) := by positivity
    have h5 : 0 < b * c := by positivity
    have h6 : 0 < b * c * b := by positivity
    field_simp [h2.ne', h3.ne']
    rw [le_div_iff (by positivity)]
    ring_nf
    nlinarith [sq_nonneg (b - c), sq_nonneg (b - 1), sq_nonneg (c - 1),
      mul_pos h2 h3, mul_pos h2 h4, mul_pos h3 h4]
  exact h_main
