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
    have h1 : (x / 50) * 50 = 40 * 50  := by
        linarith
    have h2 : x = 40 * 50  := by
        linarith
    have h3 : 40 * 50 = 2000  := by
        linarith
    linarith