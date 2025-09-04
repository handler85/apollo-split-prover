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
theorem mathd_numbertheory_235 : (29 * 79 + 31 * 81) % 10 = 2 := by
  have step1 : (29 * 79) % 10 = ((29 % 10) * (79 % 10)) % 10  := by
      omega
  have r29 : 29 % 10 = 9  := by
    omega
  have r79 : 79 % 10 = 9  := by
      gcongr
  have step3a : (29 * 79) % 10 = (9 * 9) % 10  := by
      gcongr
  have step4a : (9 * 9) % 10 = 81 % 10  := by
      gcongr
  have mod81 : 81 % 10 = 1  := by
      gcongr
  have prod1 : (29 * 79) % 10 = 1  := by
      gcongr
  have step6 : (31 * 81) % 10 = ((31 % 10) * (81 % 10)) % 10  := by
    gcongr
  have r31 : 31 % 10 = 1  := by
    gcongr
  have r81 : 81 % 10 = 1  := by
      gcongr
  have prod2 : (31 * 81) % 10 = (1 * 1) % 10  := by
    gcongr
  have prod2_eq : (31 * 81) % 10 = 1  := by
      gcongr
  have add_mod : ((29 * 79 + 31 * 81) % 10) = (((29 * 79) % 10 + (31 * 81) % 10) % 10)  := by
      omega
  have sum_mod : ((29 * 79) % 10 + (31 * 81) % 10) % 10 = (1 + 1) % 10  := by
      gcongr
  have final_step : (1 + 1) % 10 = 2  := by
      gcongr
  exact try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
  sorry
