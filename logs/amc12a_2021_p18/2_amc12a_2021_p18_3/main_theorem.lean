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
lemma amc12a_2021_p18_3
  (f : ℚ → ℝ)
  (p n : ℕ)
  (h₀ : ∀ (x : ℚ), (0 : ℚ) < x → ∀ (y : ℚ), (0 : ℚ) < y → f (x * y) = f x + f y)
  (h₁ : ∀ (p : ℕ), Nat.Prime p → f (↑p : ℚ) = (↑p : ℝ))
  (f_one : f (1 : ℚ) = (0 : ℝ))
  (f_inv : ∀ (x : ℚ), (0 : ℚ) < x → f x⁻¹ = -f x)
  (hp : Nat.Prime p)
  (ih : f ((↑p : ℚ) ^ n) = (↑n : ℝ) * (↑p : ℝ)) :
  f ((↑p : ℚ) * (↑p : ℚ) ^ n) = (↑n : ℝ) * (↑p : ℝ) + (↑p : ℝ) := by
  have h_main : f ((↑p : ℚ) * (↑p : ℚ) ^ n) = f ((↑p : ℚ)) + f ((↑p : ℚ) ^ n) := by
    have h₂ : (0 : ℚ) < (p : ℚ) := by
      exact_mod_cast Nat.Prime.pos hp
    have h₃ : (0 : ℚ) < ((p : ℚ) : ℚ) ^ n := by
      exact pow_pos h₂ n
    have h₄ : f ((↑p : ℚ) * (↑p : ℚ) ^ n) = f ((↑p : ℚ)) + f ((↑p : ℚ) ^ n) := by
      have h₅ := h₀ (p : ℚ) h₂ ((↑p : ℚ) ^ n) h₃
      simpa [mul_comm] using h₅
    exact h₄
  
  have h_final : f ((↑p : ℚ) * (↑p : ℚ) ^ n) = (↑n : ℝ) * (↑p : ℝ) + (↑p : ℝ) := by
    have h₂ : f ((↑p : ℚ)) = (↑p : ℝ) := by
      have h₃ : f (↑p : ℚ) = (↑p : ℝ) := by
        exact h₁ p hp
      exact h₃
    have h₃ : f ((↑p : ℚ) * (↑p : ℚ) ^ n) = f ((↑p : ℚ)) + f ((↑p : ℚ) ^ n) := h_main
    rw [h₃]
    have h₄ : f ((↑p : ℚ) ^ n) = (↑n : ℝ) * (↑p : ℝ) := by
      simpa using ih
    rw [h₂, h₄]
    <;> ring
    <;> field_simp
    <;> linarith
  
  exact h_final
