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
theorem amc12a_2021_p9 : (∏ k in Finset.range 7, (2 ^ (2 ^ k) + 3 ^ (2 ^ k))) = 3 ^ 128 - 2 ^ 128 := by
  have telescoping_identity : 3 ^ 128 - 2 ^ 128 = (3 - 2) * (∏ k in Finset.range 7, (2 ^ (2 ^ k) + 3 ^ (2 ^ k)))  := by
    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
  have one_sub : 3 - 2 = 1  := by
    simp
  rw [one_sub] at telescoping_identity
  exact telescoping_identitydecide