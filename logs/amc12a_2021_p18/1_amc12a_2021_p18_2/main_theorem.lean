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

lemma amc12a_2021_p18_2
  (f : ℚ → ℝ)
  (x : ℚ)
  (h₀ : ∀ (x : ℚ), (0 : ℚ) < x → ∀ (y : ℚ), (0 : ℚ) < y → f (x * y) = f x + f y)
  (h₁ : ∀ (p : ℕ), Nat.Prime p → f (↑p : ℚ) = (↑p : ℝ))
  (f_one : f (1 : ℚ) = (0 : ℝ))
  (hx : (0 : ℚ) < x) :
  f x⁻¹ = -f x := by
  have h_main : f (x * x⁻¹) = f x + f x⁻¹ := by
    have h₂ := h₀ x hx (x⁻¹) (by
      -- Prove that x⁻¹ is positive since x is positive
      exact inv_pos.mpr hx)
    simpa [mul_comm] using h₂
  
  have h_product : x * x⁻¹ = (1 : ℚ) := by
    have h₂ : x ≠ 0 := by positivity
    field_simp [h₂]
    <;> ring_nf
    <;> simp_all
    <;> aesop
  
  have h_f_one : f (x * x⁻¹) = (0 : ℝ) := by
    rw [h_product]
    simp [f_one]
    <;> norm_cast
    <;> simp_all
  
  have h_final : f x⁻¹ = -f x := by
    have h₃ : f (x * x⁻¹) = f x + f x⁻¹ := h_main
    have h₄ : f (x * x⁻¹) = (0 : ℝ) := h_f_one
    have h₅ : f x + f x⁻¹ = 0 := by linarith
    have h₆ : f x⁻¹ = -f x := by linarith
    exact h₆
  
  exact h_final
