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
theorem mathd_algebra_342 (a d : ℝ)
    (h₀ : (∑ k in Finset.range 5, (a + k * d)) = 70)
    (h₁ : (∑ k in Finset.range 10, (a + k * d)) = 210) : a = 42 / 5 := by
    have sum5_closed : 5 * a + 10 * d = 70 := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
        sorry
    have eq1 : a + 2 * d = 14 := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
        sorry
    have sum10_closed : 10 * a + 45 * d = 210 := by
        linarith
    have eq2 : 2 * a + 9 * d = 42 := by
        linarith
    have d_value : d = 14 / 5 := by
        linarith
    --have a_value : a = 14 - 2 * (14 / 5) := by
        --linarith
        --
    
    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
    sorry