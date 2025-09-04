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
theorem mathd_algebra_354 (a d : ℝ) (h₀ : a + 6 * d = 30) (h₁ : a + 10 * d = 60) :
    a + 20 * d = 135 := by
    have h_d : d = 15 / 2 := by
        have h₂ : d = 15 / 2 := by
            linarith
        exact h₂
    have h_a : a = -15 := by
        have h₃ : a = -15 := by
            have h₄ : a + 6 * d = 30  := by
        
                gcongr
            rw [h_d] at h₄
            linarith
        exact h₃
    have h_main : a + 20 * d = 135 := by
        rw [h_a, h_d]
        <;> norm_num
        <;> linarith
    exact h_main