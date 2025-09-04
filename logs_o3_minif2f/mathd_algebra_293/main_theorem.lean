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
theorem mathd_algebra_293 (x : NNReal) :
    Real.sqrt (60 * x) * Real.sqrt (12 * x) * Real.sqrt (63 * x) = 36 * x * Real.sqrt (35 * x) := by 
    have h1 : Real.sqrt (60 * x) * Real.sqrt (12 * x) = Real.sqrt (60 * 12 * x * x)  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
        sorry
    have h2 : Real.sqrt (60 * 12 * x * x) * Real.sqrt (63 * x) = Real.sqrt (60 * 12 * 63 * x * x * x)  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
        sorry
    have h3 : Real.sqrt (60 * 12 * 63 * x * x * x) = Real.sqrt (1296 * 35 * x * x * x)  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
    have h4 : Real.sqrt (1296 * 35 * x * x * x) = 36 * x * Real.sqrt (35 * x)  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
        sorry
    simp_all only [ofNat_nonneg, sqrt_mul, NNReal.zero_le_coe, sqrt_mul', ofNat_pos, mul_nonneg_iff_of_pos_left, mul_nonneg_iff_of_pos_right]