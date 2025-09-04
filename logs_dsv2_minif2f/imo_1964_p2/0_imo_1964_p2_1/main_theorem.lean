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

lemma imo_1964_p2_1
  (a b c : ℝ)
  (h₀ : (0 : ℝ) < a ∧ (0 : ℝ) < b ∧ (0 : ℝ) < c)
  (h₁ : c < a + b)
  (h₂ : b < a + c)
  (h₃ : a < b + c) :
  a ^ (2 : ℕ) * (b + c - a) + b ^ (2 : ℕ) * (c + a - b) + c ^ (2 : ℕ) * (a + b - c) ≤ (3 : ℝ) * a * b * c := by
  have h_main : a ^ (2 : ℕ) * (b + c - a) + b ^ (2 : ℕ) * (c + a - b) + c ^ (2 : ℕ) * (a + b - c) ≤ (3 : ℝ) * a * b * c := by
    have h₄ : 0 < a := by linarith
    have h₅ : 0 < b := by linarith
    have h₆ : 0 < c := by linarith
    have h₇ : 0 < a * b := by positivity
    have h₈ : 0 < b * c := by positivity
    have h₉ : 0 < c * a := by positivity
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_pos h₄ h₅, mul_pos h₅ h₆, mul_pos h₆ h₄,
      mul_pos (sub_pos.mpr h₁) (sub_pos.mpr h₂), mul_pos (sub_pos.mpr h₂) (sub_pos.mpr h₃),
      mul_pos (sub_pos.mpr h₃) (sub_pos.mpr h₁),
      sq_nonneg (a + b - c), sq_nonneg (b + c - a), sq_nonneg (c + a - b)]
  exact h_main
