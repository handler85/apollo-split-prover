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
  have h1 : a ^ 2 / b + b ≥ 2 * a := by
    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


    
    have h₁ : (2 : ℝ) * a ≤ a ^ (2 : ℕ) / b + b := by
      have h₂ : 0 < b := h₀.2.1
      have h₃ : 0 < a := h₀.1
      have h₄ : 0 < a ^ (2 : ℕ) := by positivity
      have h₅ : 0 < b := by linarith
      have h₆ : 0 < a * b := by positivity
      -- Use the fact that (a - b)^2 ≥ 0 to prove the inequality
      have h₇ : (a - b) ^ 2 ≥ 0 := by nlinarith
      have h₈ : a ^ (2 : ℕ) / b + b ≥ 2 * a := by
        have h₉ : a ^ (2 : ℕ) / b + b = a ^ 2 / b + b := by norm_num
        rw [h₉]
        field_simp [h₂.ne']
        rw [le_div_iff (by positivity)]
        -- Use nlinarith to prove the inequality
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - b * 2)]
      linarith
    exact h₁


  have h2 : b ^ 2 / c + c ≥ 2 * b := by
    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


    
    have h_main : b * (2 : ℝ) ≤ b ^ (2 : ℕ) * c⁻¹ + c := by
      have h2 : 0 < b := by linarith
      have h3 : 0 < c := by linarith
      have h4 : 0 < b ^ (2 : ℕ) := by positivity
      have h5 : 0 < b * c := by positivity
      have h6 : 0 < b * c * b := by positivity
      field_simp [h2.ne', h3.ne']
      rw [le_div_iff (by positivity)]
      ring_nf
      nlinarith [sq_nonneg (b - c), sq_nonneg (b - 1), sq_nonneg (c - 1),
        mul_pos h2 h3, mul_pos h2 h4, mul_pos h3 h4]
    exact h_main


  have h3 : c ^ 2 / d + d ≥ 2 * c := by
    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


    
    have h_d_pos : d > 0 := by linarith [h₀.1, h₀.2.1, h₀.2.2.1, h₀.2.2.2]
    have h_main : c * (2 : ℝ) ≤ c ^ (2 : ℕ) * d⁻¹ + d := by
      have h₃ : 0 < c := by linarith [h₀.2.2.1]
      have h₄ : 0 < d := by linarith [h₀.2.2.2]
      have h₅ : 0 < c * d := by positivity
      have h₆ : 0 < c * d * d := by positivity
      field_simp [h₃.ne', h₄.ne']
      rw [le_div_iff (by positivity)]
      nlinarith [sq_nonneg (c - d), sq_nonneg (c + d), sq_nonneg (c - 2 * d),
        sq_nonneg (c + 2 * d), mul_pos h₃ h₄, mul_pos (mul_pos h₃ h₄) h₄,
        mul_pos (mul_pos h₃ h₄) h₃]
    exact h_main


  have h4 : d ^ 2 / a + a ≥ 2 * d := by
    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


    
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


  have sum_h : (a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a) + (a + b + c + d) ≥ 2 * (a + b + c + d)  := by
      linarith
  have final : a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d  := by
      try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


      
      have h_main : a + b + c + d ≤ a ^ (2 : ℕ) * b⁻¹ + b ^ (2 : ℕ) * c⁻¹ + c ^ (2 : ℕ) * d⁻¹ + d ^ (2 : ℕ) * a⁻¹ := by
        have h₁ : a * (2 : ℝ) ≤ a ^ (2 : ℕ) * b⁻¹ + b := h1
        have h₂ : b * (2 : ℝ) ≤ b ^ (2 : ℕ) * c⁻¹ + c := h2
        have h₃ : c * (2 : ℝ) ≤ c ^ (2 : ℕ) * d⁻¹ + d := h3
        have h₄ : d * (2 : ℝ) ≤ d ^ (2 : ℕ) * a⁻¹ + a := by
          have h₅ : d * (2 : ℝ) ≤ a + d ^ (2 : ℕ) * a⁻¹ := h4
          have h₆ : d * (2 : ℝ) ≤ d ^ (2 : ℕ) * a⁻¹ + a := by
            linarith
          exact h₆
        have h₅ : a + b + c + d ≤ a ^ (2 : ℕ) * b⁻¹ + b ^ (2 : ℕ) * c⁻¹ + c ^ (2 : ℕ) * d⁻¹ + d ^ (2 : ℕ) * a⁻¹ := by
          -- Sum the inequalities to get the desired result
          have h₆ : a * (2 : ℝ) + b * (2 : ℝ) + c * (2 : ℝ) + d * (2 : ℝ) ≤ a + a ^ (2 : ℕ) * b⁻¹ + b + b ^ (2 : ℕ) * c⁻¹ + c + c ^ (2 : ℕ) * d⁻¹ + d + d ^ (2 : ℕ) * a⁻¹ := sum_h
          have h₇ : 2 * (a + b + c + d) ≤ (a ^ (2 : ℕ) * b⁻¹ + b ^ (2 : ℕ) * c⁻¹ + c ^ (2 : ℕ) * d⁻¹ + d ^ (2 : ℕ) * a⁻¹) + (a + b + c + d) := by linarith
          have h₈ : a + b + c + d ≤ a ^ (2 : ℕ) * b⁻¹ + b ^ (2 : ℕ) * c⁻¹ + c ^ (2 : ℕ) * d⁻¹ + d ^ (2 : ℕ) * a⁻¹ := by
            linarith
          exact h₈
        exact h₅
      exact h_main


  exact final