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
theorem mathd_numbertheory_328 : 5 ^ 999999 % 7 = 6 := by
    have h1 : 5 ^ 6 % 7 = 1  := by
        omega
    have h2 : 999999 % 6 = 3  := by
        omega
    have h3 : 5 ^ 999999 % 7 = 5 ^ 3 % 7  := by
        omega
    have h4 : 5 ^ 3 % 7 = 6  := by
        omega
    linarith