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
theorem mathd_numbertheory_207 : 8 * 9 ^ 2 + 5 * 9 + 2 = 695 := by
  have step1 : 8 * 9 ^ 2 + 5 * 9 + 2 = 8 * 9 ^ 2 + 5 * 9 ^ 1 + 2 * 9 ^ 0 := by
    linarith
  have pow2 : 9 ^ 2 = 81 := by
    linarith
  have pow1 : 9 ^ 1 = 9 := by
    linarith
  have pow0 : 9 ^ 0 = 1 := by
    linarith
  have mult1 : 8 * 9 ^ 2 = 8 * 81 := by
    linarith
  have mult2 : 5 * 9 ^ 1 = 5 * 9 := by
    linarith
  have mult3 : 2 * 9 ^ 0 = 2 * 1 := by
    linarith
  have calc1 : 8 * 81 = 648 := by
    linarith
  have calc2 : 5 * 9 = 45 := by
    linarith
  have calc3 : 2 * 1 = 2 := by
    linarith
  have final_sum : 648 + 45 + 2 = 695 := by
    linarith
  exact final_sum