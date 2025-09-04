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
theorem mathd_algebra_392 (n : ℕ) (h0 : Even n)
    (h1 : (↑n - 2) ^ 2 + ↑n ^ 2 + (↑n + 2) ^ 2 = (12296 : ℤ)) :
    (↑n - 2) * ↑n * (↑n + 2) / 8 = (32736 : ℤ) := by
    have expansion : (↑n - 2)^2 + ↑n^2 + (↑n + 2)^2 = 3 * (↑n)^2 + 8 := by
        linarith
    have eq1 : 3 * (↑n)^2 + 8 = 12296 := by
        linarith
    have eq2 : 3 * (↑n)^2 = 12296 - 8 := by
        linarith
    have eq3 : (↑n)^2 = 4096 := by
        omega
    have eq4 : (↑n) = 64 := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
        sorry
    have product_calc : (64 - 2) * 64 * (64 + 2) / 8 = 32736 := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith