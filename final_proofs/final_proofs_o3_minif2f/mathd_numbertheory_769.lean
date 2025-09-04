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
theorem mathd_numbertheory_769 : (129 ^ 34 + 96 ^ 38) % 11 = 9 := by
  have h1 : 129 % 11 = 8  := by
    omega
  have h2 : 96 % 11 = 8  := by
    gcongr
  have h3 : (129 ^ 34 + 96 ^ 38) % 11 = (8 ^ 34 + 8 ^ 38) % 11  := by
    omega
  have h4 : 8 ^ 38 = 8 ^ 34 * 8 ^ 4  := by
    linarith
  have h5 : 8 ^ 34 + 8 ^ 38 = 8 ^ 34 * (1 + 8 ^ 4)  := by
    linarith
  have h6 : 8 ^ 4 % 11 = 4  := by
    omega
  have h7 : 8 ^ 34 % 11 = 8 ^ 4 % 11  := by
    omega
  have h8 : (8 ^ 34 * (1 + 8 ^ 4)) % 11 = (8 ^ 4 % 11) * (1 + (8 ^ 4 % 11)) % 11  := by
    omega
  have h9 : (8 ^ 4 % 11) * (1 + (8 ^ 4 % 11)) % 11 = (4 * (1 + 4)) % 11  := by
    omega
  have h10 : (4 * (1 + 4)) % 11 = 20 % 11  := by
    omega
  have h11 : 20 % 11 = 9  := by
    gcongr
  exact h11