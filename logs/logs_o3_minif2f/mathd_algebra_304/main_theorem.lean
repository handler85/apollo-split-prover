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
theorem mathd_algebra_304 : 91 ^ 2 = 8281 := by
    have h1 : 91 = 90 + 1  := by
        linarith
    have h2 : 91 ^ 2 = (90 + 1) ^ 2  := by
        linarith
    have h3 : (90 + 1) ^ 2 = 90 ^ 2 + 2 * 90 * 1 + 1 ^ 2  := by
        linarith
    have h4 : 90 ^ 2 = 8100  := by
        linarith
    have h5 : 2 * 90 * 1 = 180  := by
        linarith
    have h6 : 1 ^ 2 = 1  := by
        linarith
    have h7 : 8100 + 180 + 1 = 8281  := by
        linarith
    rw [h1, h2, h3, h4, h5, h6, h7]
  