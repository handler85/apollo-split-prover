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
theorem mathd_algebra_484 : Real.log 27 / Real.log 3 = 3 := by
    have h1 : 27 = 3 ^ 3  := by
        linarith
    have h2 : Real.log (3 ^ 3) = 3 * Real.log 3  := by
        simp_all only [Real.log_pow, Nat.cast_ofNat]
    have h3 : Real.log 27 = Real.log (3 ^ 3) := by
    
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
    have h4 : Real.log 27 = 3 * Real.log 3 := by
        rw [h3, h2]
    have h5 : Real.log 3 ≠ 0  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
    rw [h4]
    field_simp [h5]
  