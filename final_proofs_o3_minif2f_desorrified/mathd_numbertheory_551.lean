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
theorem mathd_numbertheory_551 : 1529 % 6 = 5 := by
  have h1 : 1529 = 6 * 254 + 5 := by
    linarith
  have h2 : 5 < 6 := by
    linarith
  have h3 : 1529 % 6 = 5 := by
    omega
  exact h3