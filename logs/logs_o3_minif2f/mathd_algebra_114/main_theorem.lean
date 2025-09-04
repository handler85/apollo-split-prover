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
theorem mathd_algebra_114 (a : ℝ) (h₀ : a = 8) :
    (16 * (a ^ 2)^(1/3))^(1/3) = 4 := by 
    have step1 : (a ^ 2)^(1/3) = a^(2/3)  := by
        linarith
    rw [step1]
    rw [h₀]
    have step2 : 8^(2/3) = (8^(1/3))^2  := by
        omega
    have step3 : 8^(1/3) = 2  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
        sorry
    have step4 : 16 * (2^2) = 64  := by
        linarith
    have step5 : 64^(1/3) = 4  := by
        omega
    omega