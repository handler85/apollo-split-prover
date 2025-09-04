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
theorem amc12a_2021_p3 (x y : ℕ) (h₀ : x + y = 17402) (h₁ : 10 ∣ x) (h₂ : x / 10 = y) :
    ↑x - ↑y = (14238 : ℤ) := by
    have h_x_div_10 : x = 10 * y := by
        have h₃ : x / 10 = y  := by
      
            gcongr
        have h₄ : x = 10 * y := by
            have h₅ : x / 10 = y  := by
        
                gcongr
            have h₆ : x = 10 * y := by
                have h₇ : x / 10 = y  := by
          
                    gcongr
                have h₈ : x = 10 * y := by
                    have h₉ : x / 10 = y  := by
            
                        gcongr
                    have h₁₀ : x = 10 * y := by
                        have h₁₁ : x / 10 = y  := by
              
                            gcongr
                        have h₁₂ : x = 10 * y := by
                            have h₁₃ : x / 10 * 10 ≤ x := by
                                apply Nat.div_mul_le_self
                            have h₁₄ : x < (y + 1) * 10 := by
                                by_contra h
                                have h₁₅ : x ≥ (y + 1) * 10  := by
                                    omega
                                have h₁₆ : x / 10 ≥ y + 1 := by
                                    have h₁₇ : x ≥ (y + 1) * 10  := by
                    
                                        gcongr
                                    have h₁₈ : x / 10 ≥ y + 1 := by
                                        omega
                                    exact h₁₈
                                omega
                            have h₁₅ : x / 10 = y  := by
                
                                gcongr
                            have h₁₆ : x = 10 * y := by
                                omega
                            exact h₁₆
                        exact h₁₂
                    exact h₁₀
                exact h₈
            exact h₆
        exact h₄
    have h_y_val : y = 1582 := by
        have h₃ : x = 10 * y  := by
      
            gcongr
        have h₄ : x + y = 17402  := by
      
            gcongr
        have h₅ : 10 * y + y = 17402 := by
            rw [h₃] at h₄
            exact h₄
        have h₆ : 11 * y = 17402 := by
            ring_nf at h₅ ⊢
            <;> omega
        have h₇ : y = 1582 := by
            omega
        exact h₇
    have h_x_val : x = 15820 := by
        have h₃ : x = 10 * y  := by
      
            gcongr
        have h₄ : y = 1582  := by
      
            gcongr
        rw [h₄] at h₃
        norm_num at h₃ ⊢
        <;> linarith
    have h_main : (x : ℤ) - y = 14238 := by
        have h₃ : x = 15820  := by
      
            gcongr
        have h₄ : y = 1582  := by
      
            gcongr
        rw [h₃, h₄]
        <;> norm_num
        <;> linarith
    exact_mod_cast h_main