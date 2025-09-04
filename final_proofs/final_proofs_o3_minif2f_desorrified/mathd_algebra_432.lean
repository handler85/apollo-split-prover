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
theorem mathd_algebra_432 (x : ℝ) : (x + 3) * (2 * x - 6) = 2 * x ^ 2 - 18 := by
    have step1 : (x + 3) * (2 * x - 6) = x * (2 * x - 6) + 3 * (2 * x - 6)  := by
        linarith
    have step2a : x * (2 * x - 6) = 2 * x ^ 2 - 6 * x  := by
        linarith
    have step2b : 3 * (2 * x - 6) = 6 * x - 18  := by
        linarith
    have step3 : (2 * x ^ 2 - 6 * x) + (6 * x - 18) = 2 * x ^ 2 - 18  := by
        linarith
    rw [step1, step2a, step2b, step3]
  