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
theorem mathd_algebra_24 (x : ℝ) (h₀ : x / 50 = 40) : x = 2000 := by
    have h₁ : x = 2000 := by
        have h₂ : x / 50 = 40  := by
      
            gcongr
        have h₃ : x = 2000 := by
            field_simp at h₂
            linarith
        exact h₃
    exact h₁