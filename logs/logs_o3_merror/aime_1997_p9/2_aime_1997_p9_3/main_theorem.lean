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

lemma aime_1997_p9_3
  (a : ℝ)
  (h₀ : (0 : ℝ) < a)
  (h₂ : (2 : ℝ) < a ^ (2 : ℕ))
  (h₃ : a ^ (2 : ℕ) < (3 : ℝ))
  (h_floor_a2 : ⌊a ^ (2 : ℕ)⌋ = (2 : ℤ))
  (eq1 : a⁻¹ = (-2 : ℝ) + a ^ (2 : ℕ)) :
  a ^ (3 : ℕ) = (1 : ℝ) + a * (2 : ℝ) := by
  have h_main : a ^ (3 : ℕ) = (1 : ℝ) + a * (2 : ℝ) := by
    have h₄ : a > 0 := h₀
    have h₅ : a⁻¹ = (-2 : ℝ) + a ^ (2 : ℕ) := eq1
    have h₆ : a ^ (2 : ℕ) = a ^ 2 := by simp [pow_two]
    rw [h₆] at h₅
    have h₇ : a ≠ 0 := by linarith
    field_simp at h₅
    ring_nf at h₅ ⊢
    nlinarith [sq_nonneg (a - 1), sq_nonneg (a - 2), sq_nonneg (a + 1),
      mul_pos h₀ (sq_pos_of_pos h₀), mul_pos (sq_pos_of_pos h₀) h₀]
  exact h_main
