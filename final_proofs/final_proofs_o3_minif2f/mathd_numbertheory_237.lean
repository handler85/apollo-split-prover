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
theorem mathd_numbertheory_237 : (∑ k in Finset.range 101, k) % 6 = 4 := by
  have h_sum_formula : (∑ k in Finset.range 101, k) = 101 * 100 / 2  := by
    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
  have h_sum_value : 101 * 100 / 2 = 5050  := by
    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
  have h_mod : 5050 % 6 = 4  := by
    decide
  rw [h_sum_formula, h_sum_value, h_mod]omegaomega