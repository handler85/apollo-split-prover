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
theorem mathd_algebra_338 (a b c : ℝ) (h₀ : 3 * a + b + c = -3) (h₁ : a + 3 * b + c = 9)
    (h₂ : a + b + 3 * c = 19) : a * b * c = -56 := by
    have h_sum_eq : 5 * (a + b + c) = (3 * a + b + c) + (a + 3 * b + c) + (a + b + 3 * c) := by
        linarith
    have h_sum_rhs : (3 * a + b + c) + (a + 3 * b + c) + (a + b + 3 * c) = (-3) + 9 + 19 := by
        linarith
    have h_total : 5 * (a + b + c) = 25 := by
        linarith
    have h_abc_sum : a + b + c = 5 := by
        linarith
    have h_sub1 : (a + 3 * b + c) - (3 * a + b + c) = 12 := by
        linarith
    have h_diff1 : -2 * a + 2 * b = 12 := by
        linarith
    have h_factor1 : 2 * (b - a) = 12 := by
        linarith
    have h_b_diff : b - a = 6 := by
        linarith
    have h_b : b = a + 6 := by
        linarith
    have h_sub2 : (a + b + 3 * c) - (3 * a + b + c) = 22 := by
        linarith
    have h_diff2 : -2 * a + 2 * c = 22 := by
        linarith
    have h_factor2 : 2 * (c - a) = 22 := by
        linarith
    have h_c_diff : c - a = 11 := by
        linarith
    have h_c : c = a + 11 := by
        linarith
    have h_substitute : a + (a + 6) + (a + 11) = 5 := by
        linarith
    have h_simpl : 3 * a + 17 = 5 := by
        linarith
    have h_a_solve : a = -4 := by
        linarith
    have h_b_val : b = (-4) + 6 := by
        linarith
    have h_b_final : b = 2 := by
        linarith
    have h_c_val : c = (-4) + 11 := by
        linarith
    have h_c_final : c = 7 := by
        linarith
    have h_product : (-4) * 2 * 7 = -56 := by
        linarith
    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith