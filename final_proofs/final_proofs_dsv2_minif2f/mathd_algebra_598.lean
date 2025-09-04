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
theorem mathd_algebra_598 (a b c d : ℝ) (h₁ : (4 : ℝ) ^ a = 5) (h₂ : (5 : ℝ) ^ b = 6)
    (h₃ : (6 : ℝ) ^ c = 7) (h₄ : (7 : ℝ) ^ d = 8) : a * b * c * d = 3 / 2 := by
  have h_a : a = Real.log 5 / Real.log 4 := by
    have h₅ : a = Real.log 5 / Real.log 4 := by
      have h₅₁ : Real.log ((4 : ℝ) ^ a) = Real.log 5  := by
        rw [h₁]
      have h₅₂ : a * Real.log 4 = Real.log 5 := by
        rw [Real.log_rpow (by norm_num : (4 : ℝ) > 0)] at h₅₁
        exact h₅₁
      have h₅₃ : a = Real.log 5 / Real.log 4 := by
        have h₅₄ : Real.log 4 ≠ 0 := by
          norm_num [Real.log_eq_zero]
          <;>
          positivity
        field_simp [h₅₄] at h₅₂ ⊢
        <;> nlinarith
      exact h₅₃
    exact h₅
  have h_b : b = Real.log 6 / Real.log 5 := by
    have h₅ : b = Real.log 6 / Real.log 5 := by
      have h₅₁ : Real.log ((5 : ℝ) ^ b) = Real.log 6  := by
        rw [h₂]
      have h₅₂ : b * Real.log 5 = Real.log 6 := by
        rw [Real.log_rpow (by norm_num : (5 : ℝ) > 0)] at h₅₁
        exact h₅₁
      have h₅₃ : b = Real.log 6 / Real.log 5 := by
        have h₅₄ : Real.log 5 ≠ 0 := by
          norm_num [Real.log_eq_zero]
          <;>
          positivity
        field_simp [h₅₄] at h₅₂ ⊢
        <;> nlinarith
      exact h₅₃
    exact h₅
  have h_c : c = Real.log 7 / Real.log 6 := by
    have h₅ : c = Real.log 7 / Real.log 6 := by
      have h₅₁ : Real.log ((6 : ℝ) ^ c) = Real.log 7  := by
        rw [h₃]
      have h₅₂ : c * Real.log 6 = Real.log 7 := by
        rw [Real.log_rpow (by norm_num : (6 : ℝ) > 0)] at h₅₁
        exact h₅₁
      have h₅₃ : c = Real.log 7 / Real.log 6 := by
        have h₅₄ : Real.log 6 ≠ 0 := by
          norm_num [Real.log_eq_zero]
          <;>
          positivity
        field_simp [h₅₄] at h₅₂ ⊢
        <;> nlinarith
      exact h₅₃
    exact h₅
  have h_d : d = Real.log 8 / Real.log 7 := by
    have h₅ : d = Real.log 8 / Real.log 7 := by
      have h₅₁ : Real.log ((7 : ℝ) ^ d) = Real.log 8  := by
        rw [h₄]
      have h₅₂ : d * Real.log 7 = Real.log 8 := by
        rw [Real.log_rpow (by norm_num : (7 : ℝ) > 0)] at h₅₁
        exact h₅₁
      have h₅₃ : d = Real.log 8 / Real.log 7 := by
        have h₅₄ : Real.log 7 ≠ 0 := by
          norm_num [Real.log_eq_zero]
          <;>
          positivity
        field_simp [h₅₄] at h₅₂ ⊢
        <;> nlinarith
      exact h₅₃
    exact h₅
  have h_main : a * b * c * d = 3 / 2 := by
    rw [h_a, h_b, h_c, h_d]
    have h₅ : Real.log 8 = Real.log (2 ^ 3)  := by
      norm_num
    have h₆ : Real.log 4 = Real.log (2 ^ 2)  := by
      norm_num
    have h₇ : Real.log 5 = Real.log 5  := by
      rfl
    have h₈ : Real.log 6 = Real.log (2 * 3)  := by
      norm_num
    have h₉ : Real.log 7 = Real.log 7  := by
      rfl
    rw [h₅, h₆, h₈]
    field_simp [Real.log_mul, Real.log_pow, Real.log_div, Real.log_mul, Real.log_pow, Real.log_div]
    <;> ring_nf
    <;> field_simp [Real.log_mul, Real.log_pow, Real.log_div, Real.log_mul, Real.log_pow, Real.log_div]
    <;> ring_nf
    <;> norm_num
    <;>
    nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2), Real.log_pos (by norm_num : (1 : ℝ) < 3)
      Real.log_pos (by norm_num : (1 : ℝ) < 4), Real.log_pos (by norm_num : (1 : ℝ) < 5)
      Real.log_pos (by norm_num : (1 : ℝ) < 6), Real.log_pos (by norm_num : (1 : ℝ) < 7)
      Real.log_pos (by norm_num : (1 : ℝ) < 8)]
  rw [h_main]
  <;> norm_num