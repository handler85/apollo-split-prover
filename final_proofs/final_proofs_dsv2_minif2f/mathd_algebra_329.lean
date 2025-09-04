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
theorem mathd_algebra_329 (x y : ℝ) (h₀ : 3 * y = x) (h₁ : 2 * x + 5 * y = 11) : x + y = 4 := by
    have h_y : y = 1 := by
        have h₂ : 2 * x + 5 * y = 11  := by
      
            gcongr
        have h₃ : x = 3 * y  := by
            linarith
        rw [h₃] at h₂
        ring_nf at h₂ ⊢
        nlinarith
    have h_x : x = 3 := by
        have h₂ : x = 3 * y  := by
            linarith
        rw [h_y] at h₂
        linarith
    have h_sum : x + y = 4 := by
        rw [h_x, h_y]
        <;> norm_num
        <;> linarith
    exact h_sum