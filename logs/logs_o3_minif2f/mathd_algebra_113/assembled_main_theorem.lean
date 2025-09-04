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
theorem mathd_algebra_113 (x : ℝ) : x ^ 2 - 14 * x + 3 ≥ 7 ^ 2 - 14 * 7 + 3 := by
    have h1 : x ^ 2 - 14 * x + 3 = (x - 7) ^ 2 - 46  := by
        linarith
    have h2 : (x - 7) ^ 2 ≥ 0  := by
        exact sq_nonneg (x - (7 : ℝ))
    have h3 : (x - 7) ^ 2 - 46 ≥ -46  := by
        linarith
    have h4 : 7 ^ 2 - 14 * 7 + 3 = -46  := by
        linarith
    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith