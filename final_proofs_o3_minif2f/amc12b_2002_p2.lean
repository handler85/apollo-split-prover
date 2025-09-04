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
theorem amc12b_2002_p2 (x : ℤ) (h₀ : x = 4) :
    (3 * x - 2) * (4 * x + 1) - (3 * x - 2) * (4 * x) + 1 = 11 := by
    have step1 : (3 * x - 2) * (4 * x + 1) - (3 * x - 2) * (4 * x) = (3 * x - 2) * ((4 * x + 1) - (4 * x))  := by
        linarith
    have step2 : (4 * x + 1) - (4 * x) = 1  := by
        linarith
    have step3 : (3 * x - 2) * ((4 * x + 1) - (4 * x)) = (3 * x - 2) * 1  := by
        linarith
    have step4 : (3 * x - 2) * 1 = 3 * x - 2  := by
        linarith
    have step5 : (3 * x - 2) + 1 = 3 * x - 1  := by
        linarith
    have step6 : 3 * x - 1 = 3 * 4 - 1  := by
        linarith
    have step7 : 3 * 4 - 1 = 11  := by
        linarith
  
    linarith