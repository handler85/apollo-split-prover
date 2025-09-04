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
theorem algebra_sqineq_unitcircatbpabsamblt1 (a b : ℝ) (h₀ : a ^ 2 + b ^ 2 = 1) :
    a * b + abs (a - b) ≤ 1 := by
    have h_main : a * b + abs (a - b) ≤ 1 := by
        cases' le_total 0 (a - b) with h h
        · -- Case 1: a - b ≥ 0, i.e., a ≥ b
            have h₁ : abs (a - b) = a - b := by
                rw [abs_of_nonneg h]
            rw [h₁]
            --nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a - b - 1)
                --sq_nonneg (a + b - 1), sq_nonneg (a + b + 1), sq_nonneg (a - b + 1)
        
            try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


            
            have h_main : a + (a * b - b) ≤ (1 : ℝ) := by
              have h₁ : a ^ 2 + b ^ 2 = 1 := by
                norm_cast at h₀ ⊢
                <;>
                (try ring_nf at h₀ ⊢ <;> simp_all) <;>
                nlinarith
              nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (a + b), sq_nonneg (a - b),
                sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), mul_self_nonneg (a - b),
                mul_self_nonneg (a + b - 1), mul_self_nonneg (a + b + 1),
                mul_self_nonneg (a * b - 1 / 4)]
            
            exact h_main


        · -- Case 2: a - b ≤ 0, i.e., a ≤ b
            have h₁ : abs (a - b) = -(a - b) := by
                rw [abs_of_nonpos h]
                <;> linarith
            rw [h₁]
            --nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a - b - 1)
                --sq_nonneg (a + b - 1), sq_nonneg (a + b + 1), sq_nonneg (a - b + 1)
        
            try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


            
            have h₂ : a ≥ -1 := by
              have h₂₁ : a ^ 2 ≤ 1 := by
                nlinarith [sq_nonneg (b : ℝ), sq_nonneg (a - b : ℝ)]
              nlinarith [sq_nonneg (a + 1 : ℝ), sq_nonneg (a - 1 : ℝ)]
            
            have h₃ : b ≤ 1 := by
              have h₃₁ : b ^ 2 ≤ 1 := by
                nlinarith [sq_nonneg (a : ℝ), sq_nonneg (a - b : ℝ)]
              nlinarith [sq_nonneg (b - 1 : ℝ), sq_nonneg (b + 1 : ℝ)]
            
            have h₄ : -a + a * b + b ≤ 1 := by
              cases' le_or_lt 0 (a - b) with h₅ h₅
              · -- Case 1: a - b ≥ 0
                have h₆ : |a - b| = a - b := by
                  rw [abs_of_nonneg h₅]
                  <;> linarith
                have h₇ : a - b = -a + b := by
                  linarith
                have h₈ : a = b := by linarith
                rw [h₈] at h₀ ⊢
                nlinarith [sq_nonneg (b : ℝ), sq_nonneg (b - 1 : ℝ)]
              · -- Case 2: a - b < 0
                have h₆ : |a - b| = -(a - b) := by
                  rw [abs_of_neg h₅]
                  <;> linarith
                have h₇ : -(a - b) = -a + b := by linarith
                have h₈ : (a - b) = a - b := by linarith
                nlinarith [sq_nonneg (a + 1 : ℝ), sq_nonneg (b - 1 : ℝ),
                  sq_nonneg (a - b : ℝ), sq_nonneg (a + b : ℝ),
                  sq_nonneg (a - 1 : ℝ), sq_nonneg (b + 1 : ℝ)]
            exact h₄


    exact h_main