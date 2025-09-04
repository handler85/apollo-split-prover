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
theorem mathd_algebra_160 (n x : ℝ) (h₀ : n + x = 97) (h₁ : n + 5 * x = 265) : n + 2 * x = 139 := by
    have h_x : x = 42 := by
        have h₂ : x = 42 := by
            have h₃ : n + 5 * x = 265  := by
        
                gcongr
            have h₄ : n + x = 97  := by
        
                gcongr
            linarith
        exact h₂
    have h_n : n = 55 := by
        have h₂ : n + x = 97  := by
      
            gcongr
        have h₃ : x = 42  := by
      
            gcongr
        have h₄ : n = 55 := by
            rw [h₃] at h₂
            linarith
        exact h₄
    have h_main : n + 2 * x = 139 := by
        have h₃ : n = 55  := by
      
            gcongr
        have h₄ : x = 42  := by
      
            gcongr
        rw [h₃, h₄]
        <;> norm_num
        <;> linarith
    exact h_main