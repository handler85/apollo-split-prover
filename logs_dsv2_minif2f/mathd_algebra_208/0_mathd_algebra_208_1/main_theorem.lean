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
lemma mathd_algebra_208_1
    (h₁ h_sqrt : True) :
    (1000000 : ℝ) ^ (1 / 3 : ℝ) = (100 : ℝ) := by
        norm_num <;>
        norm_num <;>
        norm_num <;>
        simp_all [Real.rpow_def_of_pos, Real.exp_log, Real.log_rpow, mul_comm]
        <;>
        norm_num
        <;>
        ring_nf
        <;>
        norm_num
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
        sorry