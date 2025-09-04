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

lemma mathd_algebra_487_1
  (a b c d : ℝ)
  (h₀ : b = a ^ (2 : ℕ))
  (h₁ : a + a ^ (2 : ℕ) = (1 : ℝ))
  (h₂ : d = c ^ (2 : ℕ))
  (h₃ : c + c ^ (2 : ℕ) = (1 : ℝ))
  (h₄ : ¬a = c)
  (h₇ : a + c = (-1 : ℝ))
  (h₆ : (-1 : ℝ) + c + c ^ (2 : ℕ) = (0 : ℝ))
  (h₅ : (-1 : ℝ) + a + a ^ (2 : ℕ) = (0 : ℝ)) :
  -(a * c * (2 : ℝ)) + a ^ (2 : ℕ) + c ^ (2 : ℕ) = (5 : ℝ) := by
  have h₈ : a ^ 2 + c ^ 2 = 3 := by
    have h₈₁ : a + a ^ 2 = 1 := by
      simpa [pow_two] using h₁
    have h₈₂ : c + c ^ 2 = 1 := by
      simpa [pow_two] using h₃
    have h₈₃ : a ^ 2 + c ^ 2 = 3 := by
      nlinarith [sq_nonneg (a + c), sq_nonneg (a - c)]
    exact h₈₃
  
  have h₉ : a * c = -1 := by
    have h₉₁ : a + c = -1 := by linarith
    have h₉₂ : a ^ 2 + c ^ 2 = 3 := h₈
    have h₉₃ : (a + c) ^ 2 = a ^ 2 + c ^ 2 + 2 * (a * c) := by
      ring
    rw [h₉₁] at h₉₃
    nlinarith [sq_nonneg (a - c)]
  
  have h₁₀ : -(a * c * (2 : ℝ)) + a ^ (2 : ℕ) + c ^ (2 : ℕ) = (5 : ℝ) := by
    simp [pow_two] at h₁ h₃ h₅ h₆ h₈ h₉ ⊢
    nlinarith [sq_nonneg (a - c), sq_nonneg (a + c), sq_nonneg (a + 1), sq_nonneg (c + 1),
      sq_nonneg (a - 1), sq_nonneg (c - 1)]
  
  exact h₁₀
