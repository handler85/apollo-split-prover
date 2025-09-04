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
theorem amc12a_2009_p6 (m n p q : ℝ) (h₀ : p = 2 ^ m) (h₁ : q = 3 ^ n) :
    p ^ (2 * n) * q ^ m = 12 ^ (m * n) := by
    have h12 : 12 = 2 ^ 2 * 3  := by
        linarith
    have h_p : p ^ (2 * n) = (2 ^ m) ^ (2 * n) := by
        rw [h₀]
    have h_q : q ^ m = (3 ^ n) ^ m := by
        rw [h₁]
    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
    sorry