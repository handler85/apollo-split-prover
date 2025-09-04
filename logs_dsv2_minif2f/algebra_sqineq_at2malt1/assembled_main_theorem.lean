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
theorem algebra_sqineq_at2malt1 (a : ℝ) : a * (2 - a) ≤ 1 := by
    have h_main : a * (2 - a) ≤ 1 := by
        have h₁ : a * (2 - a) = 2 * a - a ^ 2 := by
            ring
        rw [h₁]
        have h₂ : 2 * a - a ^ 2 ≤ 1 := by
            --nlinarith [sq_nonneg (a - 1), sq_nonneg (a - 1 / 2), sq_nonneg (a + 1), sq_nonneg (a + 1 / 2)
                --sq_nonneg (a - 2), sq_nonneg (a + 2), sq_nonneg (a - 1 / 2 - 1), sq_nonneg (a + 1 / 2 - 1)
        
            try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


            
            have h_main : (2 : ℝ) * a ≤ (1 : ℝ) + a ^ (2 : ℕ) := by
              norm_num [pow_two] at h₁ ⊢
              nlinarith [sq_nonneg (a - 1)]
            exact h_main


        linarith
    exact h_main