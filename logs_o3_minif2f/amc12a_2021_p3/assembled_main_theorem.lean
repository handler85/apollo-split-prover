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
theorem amc12a_2021_p3 (x y : ℕ) 
    (h₀ : x + y = 17402) 
    (h₁ : 10 ∣ x) 
    (h₂ : x / 10 = y) :
    ↑x - ↑y = (14238 : ℤ) := by
    have h_eq : x = 10 * y := by
        omega
    have h_sum : 11 * y = 17402 := by
        linarith
    have h_y : y = 17402 / 11 := by
        omega
    --have h_x : x = 10 * (17402 / 11) := by
        --linarith
    ----have h_diff : 9 * (17402 / 11) = 14238 := by
        ----try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
        ----
        --
    
    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith