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

lemma amc12a_2021_p18_6
  (f : ℚ → ℝ)
  (h₀ : ∀ (x : ℚ), (0 : ℚ) < x → ∀ (y : ℚ), (0 : ℚ) < y → f (x * y) = f x + f y)
  (h₁ : ∀ (p : ℕ), Nat.Prime p → f (↑p : ℚ) = (↑p : ℝ))
  (f_one : f (1 : ℚ) = (0 : ℝ))
  (f_inv : ∀ (x : ℚ), (0 : ℚ) < x → f x⁻¹ = -f x)
  (f_pow : ∀ (p n : ℕ), Nat.Prime p → f ((↑p : ℚ) ^ n) = (↑n : ℝ) * (↑p : ℝ))
  (f_25 : f (25 : ℚ) = (10 : ℝ))
  (f_11 : f (11 : ℚ) = (11 : ℝ)) :
  f (25 / 11 : ℚ) = (-1 : ℝ) := by
  have h_f_inv_11 : f (11 : ℚ) = (11 : ℝ) := by
    simpa [h₁] using f_11
  
  have h_f_inv_5 : f (5 : ℚ) = (5 : ℝ) := by
    have h2 : f (5 : ℚ) = (5 : ℝ) := by
      have h3 := h₀ 5 (by norm_num) 5 (by norm_num)
      have h4 := h₀ 5 (by norm_num) (1 / 5 : ℚ) (by norm_num)
      have h5 := h₀ (11 : ℚ) (by norm_num) (1 / 11 : ℚ) (by norm_num)
      have h6 := h₀ (25 : ℚ) (by norm_num) (1 / 25 : ℚ) (by norm_num)
      norm_num [f_one, f_inv, f_pow, h₁, Nat.cast_one] at *
      <;>
      (try ring_nf at * <;> nlinarith) <;>
      (try linarith [h₁ 5 (by decide), h₁ 11 (by decide), h₁ 25 (by decide)]) <;>
      (try field_simp [h₁] at *) <;>
      (try norm_cast at *) <;>
      (try linarith)
    exact h2
  
  have h_f_inv_inv_11 : f ((11 : ℚ)⁻¹) = (-(11 : ℝ)) := by
    have h₂ : f ((11 : ℚ)⁻¹) = -f (11 : ℚ) := by
      apply f_inv 11
      norm_num
    rw [h₂]
    <;> simp [h_f_inv_11]
    <;> norm_num
    <;> linarith
  
  have h_f_inv_25 : f ((25 : ℚ) / 11) = (-1 : ℝ) := by
    have h₃ : f ((25 : ℚ) / 11) = f (25 : ℚ) + f ((11 : ℚ)⁻¹) := by
      have h₄ := h₀ (25 : ℚ) (by norm_num) ((11 : ℚ)⁻¹) (by norm_num)
      norm_num at h₄ ⊢
      <;>
      ring_nf at h₄ ⊢ <;>
      nlinarith
    rw [h₃]
    have h₄ : f (25 : ℚ) = (10 : ℝ) := f_25
    have h₅ : f ((11 : ℚ)⁻¹) = (-(11 : ℝ)) := h_f_inv_inv_11
    rw [h₄, h₅]
    <;> norm_num
    <;> linarith
  
  exact h_f_inv_25
