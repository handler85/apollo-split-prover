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

lemma algebra_amgm_sumasqdivbgeqsuma_4
  (a b c d : ℝ)
  (h₀ : (0 : ℝ) < a ∧ (0 : ℝ) < b ∧ (0 : ℝ) < c ∧ (0 : ℝ) < d)
  (h3 : c * (2 : ℝ) ≤ d + c ^ (2 : ℕ) * d⁻¹)
  (h2 : b * (2 : ℝ) ≤ c + b ^ (2 : ℕ) * c⁻¹)
  (h1 : a * (2 : ℝ) ≤ a ^ (2 : ℕ) * b⁻¹ + b) :
  d * (2 : ℝ) ≤ d ^ (2 : ℕ) * a⁻¹ + a := by
  have h_main : d * (2 : ℝ) ≤ d ^ (2 : ℕ) * a⁻¹ + a := by
    have h₁ : 0 < a := by linarith
    have h₂ : 0 < d := by linarith
    have h₃ : 0 < a * d := by positivity
    field_simp [h₁.ne', h₂.ne']
    rw [le_div_iff (by positivity)]
    -- Simplify the inequality to a form that can be directly verified.
    ring_nf
    nlinarith [sq_nonneg (d - a), sq_nonneg (a - d), sq_nonneg (a - 2 * d),
      sq_nonneg (d - 2 * a), mul_pos h₁ h₂, mul_pos (mul_pos h₁ h₂) h₁,
      mul_pos (mul_pos h₁ h₂) h₂]
  exact h_main
