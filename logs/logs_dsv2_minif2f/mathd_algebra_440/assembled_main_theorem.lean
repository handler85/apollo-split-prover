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
theorem mathd_algebra_440 (x : ℝ) (h₀ : 3 / 2 / 3 = x / 10) : x = 5 := by
    have h₁ : x = 5 := by
        have h₂ : (3 / 2 / 3 : ℝ) = x / 10  := by
      
            gcongr
        have h₃ : (3 / 2 / 3 : ℝ) = 1 / 2  := by
            norm_num
        rw [h₃] at h₂
        have h₄ : (1 / 2 : ℝ) = x / 10  := by
            linarith
        have h₅ : x = 5 := by
            field_simp at h₄
            <;> linarith
        exact h₅
    exact h₁