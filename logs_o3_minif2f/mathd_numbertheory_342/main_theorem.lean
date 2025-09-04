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
theorem mathd_numbertheory_342 : 54 % 6 = 0 := by
  have h1 : 54 = 6 * 9 := by
    linarith
  have h2 : 6 ∣ 54 := by
    omega
  have h3 : 54 % 6 = 0 := by
    omega
  exact h3