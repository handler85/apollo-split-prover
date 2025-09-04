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
theorem mathd_algebra_359 (y : ℝ) (h₀ : y + 6 + y = 2 * 12) : y = 9 := by
    have h1 : 2 * 12 = 24 := by
        linarith
    have h2 : y + 6 + y = 24 := by
    
    
        linarith
    have h3 : 2 * y + 6 = 24 := by
        linarith
    have h4 : 2 * y = 18 := by
        linarith
    have h5 : y = 9 := by
        linarith
    exact h5