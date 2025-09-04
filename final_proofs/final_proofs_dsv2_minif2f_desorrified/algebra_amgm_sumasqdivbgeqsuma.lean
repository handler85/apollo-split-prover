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
theorem algebra_amgm_sumasqdivbgeqsuma (a b c d : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) :
    a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d := by
  have h_main : a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d := by
    have h₁ : a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d := by
      have h₂ : 0 < a  := by
        linarith
      have h₃ : 0 < b  := by
        linarith
      have h₄ : 0 < c  := by
        linarith
      have h₅ : 0 < d  := by
        linarith
      have h₆ : 0 < a * b  := by
        positivity
      have h₇ : 0 < b * c  := by
        positivity
      have h₈ : 0 < c * d  := by
        positivity
      have h₉ : 0 < d * a  := by
        positivity
      have h₁₀ : a ^ 2 / b + b ≥ 2 * a := by
        have h₁₀ : 0 < b  := by
          linarith
        have h₁₁ : 0 < a  := by
          linarith
        field_simp [h₁₀.ne', h₁₁.ne']
        rw [le_div_iff (by positivity)]
        nlinarith [sq_nonneg (a - b)]
      have h₁₁ : b ^ 2 / c + c ≥ 2 * b := by
        have h₁₁ : 0 < c  := by
          linarith
        have h₁₂ : 0 < b  := by
          linarith
        field_simp [h₁₁.ne', h₁₂.ne']
        rw [le_div_iff (by positivity)]
        nlinarith [sq_nonneg (b - c)]
      have h₁₂ : c ^ 2 / d + d ≥ 2 * c := by
        have h₁₂ : 0 < d  := by
          linarith
        have h₁₃ : 0 < c  := by
          linarith
        field_simp [h₁₂.ne', h₁₃.ne']
        rw [le_div_iff (by positivity)]
        nlinarith [sq_nonneg (c - d)]
      have h₁₃ : d ^ 2 / a + a ≥ 2 * d := by
        have h₁₃ : 0 < a  := by
          linarith
        have h₁₄ : 0 < d  := by
          linarith
        field_simp [h₁₃.ne', h₁₄.ne']
        rw [le_div_iff (by positivity)]
        nlinarith [sq_nonneg (d - a)]
      have h₁₄ : a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a + (a + b + c + d) ≥ 2 * (a + b + c + d) := by
        linarith
      have h₁₅ : a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d := by
        linarith
      exact h₁₅
    exact h₁
  exact h_main