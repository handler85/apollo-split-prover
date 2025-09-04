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
theorem mathd_numbertheory_85 : 1 * 3 ^ 3 + 2 * 3 ^ 2 + 2 * 3 + 2 = 53 := by
  have h1 : 3^3 = 27  := by
    linarith
  have h2 : 3^2 = 9  := by
    linarith
  have h3 : 1 * 3^3 = 27  := by
    linarith -- uses h1
  have h4 : 2 * 3^2 = 18  := by
    linarith -- uses h2
  have h5 : 2 * 3 = 6  := by
    linarith -- computes 2 * 3
  have h6 : 2 * 3^0 = 2  := by
    linarith -- since 3^0 = 1
  have h7 : 27 + 18 + 6 + 2 = 53  := by
    linarith
  exact h7