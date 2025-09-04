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

lemma mathd_algebra_129_1
  (a : ℝ)
  (h₀ : ¬a = (0 : ℝ))
  (h₁ : (1 / 2 : ℝ) - a⁻¹ = (1 : ℝ)) :
  a = (-2 : ℝ) := by
  have h₂ : a⁻¹ = (-1 / 2 : ℝ) := by
    have h₂₁ : (1 / 2 : ℝ) - a⁻¹ = (1 : ℝ) := h₁
    have h₂₂ : a⁻¹ = (1 / 2 : ℝ) - 1 := by linarith
    have h₂₃ : a⁻¹ = (-1 / 2 : ℝ) := by linarith
    exact h₂₃
  
  have h₃ : a = (-2 : ℝ) := by
    have h₃₁ : a ≠ 0 := by
      intro h
      apply h₀
      linarith
    have h₃₂ : a⁻¹ = (-1 / 2 : ℝ) := h₂
    have h₃₃ : a = (-2 : ℝ) := by
      have h₃₄ : a⁻¹ = (-1 / 2 : ℝ) := h₂
      have h₃₅ : a ≠ 0 := h₃₁
      field_simp at h₃₄ ⊢
      nlinarith
    exact h₃₃
  
  rw [h₃]
  <;> norm_num
  <;> simp_all
  <;> field_simp at *
  <;> linarith
