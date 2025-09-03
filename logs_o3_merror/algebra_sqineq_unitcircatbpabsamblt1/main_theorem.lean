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
theorem algebra_sqineq_unitcircatbpabsamblt1 (a b : ℝ) (h₀ : a ^ 2 + b ^ 2 = 1) :
    a * b + abs (a - b) ≤ 1 := by 
    --have h_diff_sq : (a - b)^2 = 1 - 2 * a * b  := by
        --
    
    
    have h_abs : abs (a - b) = sqrt (1 - 2 * a * b) := by
        linarith
    have h_goal : a * b + sqrt (1 - 2 * a * b) ≤ 1  := by
        gcongr
    have h_reduction : sqrt (1 - 2 * a * b) ≤ 1 - a * b  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
        sorry
    have h_sq : (sqrt (1 - 2 * a * b))^2 ≤ (1 - a * b)^2  := by
        linarith
    have h_expand : 1 - 2 * a * b ≤ 1 - 2 * a * b + (a * b)^2  := by
        linarith
    have h_nonneg : 0 ≤ (a * b)^2  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith