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
theorem amc12a_2013_p4 : (2 ^ 2014 + 2 ^ 2012) / (2 ^ 2014 - 2 ^ 2012) = (5 : ℝ) / 3 := by
    have h1 : 2 ^ 2014 = 2 ^ 2012 * 2 ^ 2  := by
        linarith
    have h2 : 2 ^ 2014 + 2 ^ 2012 = 2 ^ 2012 * (2 ^ 2 + 1)  := by
        linarith
    have h3 : 2 ^ 2014 - 2 ^ 2012 = 2 ^ 2012 * (2 ^ 2 - 1)  := by
        omega
    have h4 : 2 ^ 2012 ≠ 0  := by
        linarith
    have h5 : (2 ^ 2012 * (2 ^ 2 + 1)) / (2 ^ 2012 * (2 ^ 2 - 1)) = (2 ^ 2 + 1) / (2 ^ 2 - 1)  := by
        omega
    have h6 : 2 ^ 2 = 4  := by
        linarith
    have h7 : (2 ^ 2 + 1) = 4 + 1  := by
        linarith
    have h8 : (2 ^ 2 - 1) = 4 - 1  := by
        omega
    have h9 : (4 + 1) / (4 - 1) = 5 / 3  := by
        omega
    linarith