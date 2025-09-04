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
theorem mathd_algebra_293 (x : NNReal) :
    Real.sqrt (60 * x) * Real.sqrt (12 * x) * Real.sqrt (63 * x) = 36 * x * Real.sqrt (35 * x) := by 
    have h1 : Real.sqrt (60 * x) * Real.sqrt (12 * x) = Real.sqrt (60 * 12 * x * x)  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


        
        have h_main : √(60 : ℝ) * √(↑x : ℝ) * (√(12 : ℝ) * √(↑x : ℝ)) = √(720 : ℝ) * √(↑x : ℝ) * √(↑x : ℝ) := by
          have h₀ : √(60 : ℝ) * √(↑x : ℝ) * (√(12 : ℝ) * √(↑x : ℝ)) = √(60 : ℝ) * √(12 : ℝ) * (√(↑x : ℝ) * √(↑x : ℝ)) := by
            ring_nf
            <;>
            field_simp <;>
            ring_nf <;>
            norm_num <;>
            nlinarith [Real.sqrt_nonneg (60 : ℝ), Real.sqrt_nonneg (12 : ℝ), Real.sqrt_nonneg (↑x : ℝ)]
          rw [h₀]
          have h₁ : √(60 : ℝ) * √(12 : ℝ) = √(60 * 12 : ℝ) := by
            rw [← Real.sqrt_mul (by positivity)]
            <;> ring_nf
          rw [h₁]
          have h₂ : √(60 * 12 : ℝ) = √(720 : ℝ) := by
            norm_num
            <;>
            rw [Real.sqrt_eq_iff_sq_eq] <;>
            norm_num <;>
            ring_nf <;>
            norm_num
            <;>
            nlinarith [Real.sqrt_nonneg (720 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 720 by norm_num)]
          rw [h₂]
          <;> ring_nf
          <;> field_simp [Real.sqrt_eq_iff_sq_eq] <;> ring_nf <;> norm_num <;>
          nlinarith [Real.sqrt_nonneg (720 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 720 by norm_num),
            Real.sqrt_nonneg (↑x : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (↑x : ℝ) by exact_mod_cast x.prop)]
        exact h_main


    have h2 : Real.sqrt (60 * 12 * x * x) * Real.sqrt (63 * x) = Real.sqrt (60 * 12 * 63 * x * x * x)  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


        
        have h_main : √(720 : ℝ) * √(↑x : ℝ) ^ (3 : ℕ) * √(63 : ℝ) = √(↑x : ℝ) ^ (3 : ℕ) * √(45360 : ℝ) := by
          have h2 : √(720 : ℝ) * √(63 : ℝ) = √(45360 : ℝ) := by
            have h3 : √(720 : ℝ) * √(63 : ℝ) = √(720 * (63 : ℝ)) := by
              rw [← Real.sqrt_mul] <;> positivity
            rw [h3]
            have h4 : √(720 * (63 : ℝ)) = √(45360 : ℝ) := by
              norm_num [Real.sqrt_eq_iff_sq_eq]
              <;> ring_nf
              <;> norm_num
              <;> rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
              <;> nlinarith [Real.sqrt_nonneg 45360, Real.sq_sqrt (show (0 : ℝ) ≤ 45360 by norm_num)]
            rw [h4]
            <;> norm_num
          calc
            √(720 : ℝ) * √(↑x : ℝ) ^ (3 : ℕ) * √(63 : ℝ) = (√(720 : ℝ) * √(63 : ℝ)) * √(↑x : ℝ) ^ (3 : ℕ) := by ring
            _ = √(45360 : ℝ) * √(↑x : ℝ) ^ (3 : ℕ) := by rw [h2]
            _ = √(↑x : ℝ) ^ (3 : ℕ) * √(45360 : ℝ) := by ring
        exact h_main


    have h3 : Real.sqrt (60 * 12 * 63 * x * x * x) = Real.sqrt (1296 * 35 * x * x * x)  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
    have h4 : Real.sqrt (1296 * 35 * x * x * x) = 36 * x * Real.sqrt (35 * x)  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


        
        have h4 : √(45360 : ℝ) = √(60 : ℝ) * √(12 : ℝ) * √(63 : ℝ) := by
            have h4 : √(45360 : ℝ) = √(60 : ℝ) * √(12 : ℝ) * √(63 : ℝ) := by
                have h4 : √(45360 : ℝ) = √(60 : ℝ) * √(12 : ℝ) * √(63 : ℝ) := by
                    have h5 : (45360 : ℝ) = 60 * 12 * 63 := by
                        norm_num
                    have h6 : √(45360 : ℝ) = √(60 : ℝ) * √(12 : ℝ) * √(63 : ℝ) := by
                        rw [h5]
                        rw [Real.sqrt_eq_iff_sq_eq (by positivity) (by positivity)]
                        simp_all only
                        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


                        
                        have h_main : √(60 : ℝ) ^ (2 : ℕ) * √(12 : ℝ) ^ (2 : ℕ) * √(63 : ℝ) ^ (2 : ℕ) = (45360 : ℝ) := by
                          have h4 : √(60 : ℝ) ^ (2 : ℕ) * √(12 : ℝ) ^ (2 : ℕ) * √(63 : ℝ) ^ (2 : ℕ) = (60 : ℝ) * (12 : ℝ) * (63 : ℝ) := by
                            have h5 : √(60 : ℝ) ^ (2 : ℕ) = (60 : ℝ) := by
                              have h6 : √(60 : ℝ) ^ (2 : ℕ) = 60 := by
                                rw [show (√(60 : ℝ) ^ (2 : ℕ)) = (√(60 : ℝ) ^ 2) by norm_num]
                                rw [Real.sq_sqrt (by positivity)]
                                <;> norm_num
                              linarith
                            have h6 : √(12 : ℝ) ^ (2 : ℕ) = (12 : ℝ) := by
                              have h7 : √(12 : ℝ) ^ (2 : ℕ) = 12 := by
                                rw [show (√(12 : ℝ) ^ (2 : ℕ)) = (√(12 : ℝ) ^ 2) by norm_num]
                                rw [Real.sq_sqrt (by positivity)]
                                <;> norm_num
                              linarith
                            have h7 : √(63 : ℝ) ^ (2 : ℕ) = (63 : ℝ) := by
                              have h8 : √(63 : ℝ) ^ (2 : ℕ) = 63 := by
                                rw [show (√(63 : ℝ) ^ (2 : ℕ)) = (√(63 : ℝ) ^ 2) by norm_num]
                                rw [Real.sq_sqrt (by positivity)]
                                <;> norm_num
                              linarith
                            calc
                              √(60 : ℝ) ^ (2 : ℕ) * √(12 : ℝ) ^ (2 : ℕ) * √(63 : ℝ) ^ (2 : ℕ) = (60 : ℝ) * (12 : ℝ) * (63 : ℝ) := by
                                rw [h5, h6, h7]
                                <;> ring
                              _ = (60 : ℝ) * (12 : ℝ) * (63 : ℝ) := by rfl
                          have h8 : (60 : ℝ) * (12 : ℝ) * (63 : ℝ) = (45360 : ℝ) := by
                            norm_num
                          linarith
                        
                        simpa using h_main


                    rw [h6]
                    <;> ring_nf
                    <;> norm_num
                rw [h4]
            rw [h4]
            <;> ring_nf
        have h5 : √(45360 : ℝ) * √(↑x : ℝ) ^ (3 : ℕ) = √(60 : ℝ) * √(12 : ℝ) * √(63 : ℝ) * √(↑x : ℝ) ^ (3 : ℕ) := by
            rw [h4]
            <;>
            simp [mul_assoc]
            <;>
            ring_nf
            <;>
            norm_num
            <;>
            field_simp
            <;>
            ring_nf
            <;>
            norm_num
        have h7 : √(45360 : ℝ) * √(↑x : ℝ) ^ (3 : ℕ) = √(35 : ℝ) * (36 : ℝ) * √(↑x : ℝ) ^ (3 : ℕ) := by
            rw [h5]
            <;> ring_nf
            <;> ring_nf
            linarith
        have h8 : √(↑x : ℝ) * (↑x : ℝ) * √(35 : ℝ) * (36 : ℝ) = √(35 : ℝ) * (36 : ℝ) * √(↑x : ℝ) ^ (3 : ℕ) := by
            have h8 : √(↑x : ℝ) * (↑x : ℝ) = √(↑x : ℝ) ^ (3 : ℕ) := by
                try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
                try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


                
                have h_main : √(↑x : ℝ) * (↑x : ℝ) = √(↑x : ℝ) ^ (3 : ℕ) := by
                  have h5 : √(↑x : ℝ) * (↑x : ℝ) = √(↑x : ℝ) ^ (3 : ℕ) := by
                    -- Consider the cases where x = 0 or x > 0
                    have h6 : √(↑x : ℝ) * (↑x : ℝ) = √(↑x : ℝ) ^ (3 : ℕ) := by
                      -- Use the fact that √x ^ 3 = x * √x
                      have h7 : √(↑x : ℝ) ^ (3 : ℕ) = √(↑x : ℝ) ^ 2 * √(↑x : ℝ) := by
                        ring_nf
                        <;>
                        simp [pow_succ, pow_two]
                        <;>
                        ring_nf
                      rw [h7]
                      -- Simplify using the property of square roots
                      have h8 : √(↑x : ℝ) ^ 2 = (↑x : ℝ) := by
                        rw [Real.sq_sqrt (show (0 : ℝ) ≤ (↑x : ℝ) by exact by exact NNReal.coe_nonneg x)]
                      rw [h8]
                      <;>
                      ring_nf
                      <;>
                      nlinarith [Real.sqrt_nonneg (↑x : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (↑x : ℝ) by exact by exact NNReal.coe_nonneg x)]
                    exact h6
                  exact h5
                exact h_main


            try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
        have h9 : √(45360 : ℝ) * √(↑x : ℝ) ^ (3 : ℕ) = √(↑x : ℝ) * (↑x : ℝ) * √(35 : ℝ) * (36 : ℝ) := by
            have h9 : √(45360 : ℝ) * √(↑x : ℝ) ^ (3 : ℕ) = √(35 : ℝ) * (36 : ℝ) * √(↑x : ℝ) ^ (3 : ℕ) := by
                rw [h7]
            have h10 : √(↑x : ℝ) * (↑x : ℝ) * √(35 : ℝ) * (36 : ℝ) = √(35 : ℝ) * (36 : ℝ) * √(↑x : ℝ) ^ (3 : ℕ) := by
                rw [h8]
            linarith
        exact_mod_cast h9

    simp_all only [ofNat_nonneg, sqrt_mul, NNReal.zero_le_coe, sqrt_mul', ofNat_pos, mul_nonneg_iff_of_pos_left, mul_nonneg_iff_of_pos_right]