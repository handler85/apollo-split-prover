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
theorem imo_1959_p1 (n : ℕ) (h₀ : 0 < n) : Nat.gcd (21 * n + 4) (14 * n + 3) = 1 := by
    have h_step1 : (21 * n + 4) = (14 * n + 3) + (7 * n + 1) := by
        linarith
    have gcd_step1 : Nat.gcd (21 * n + 4) (14 * n + 3) = Nat.gcd (14 * n + 3) (7 * n + 1)  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


        
        have h_main : ((1 : ℕ) + n * (7 : ℕ)).gcd ((3 : ℕ) + n * (14 : ℕ)) = ((3 : ℕ) + n * (14 : ℕ)).gcd ((1 : ℕ) + n * (7 : ℕ)) := by
          rw [Nat.gcd_comm]
          <;>
          simp [Nat.gcd_comm, Nat.gcd_assoc, Nat.gcd_mul_left, Nat.gcd_mul_right, Nat.gcd_one_left, Nat.gcd_one_right]
          <;>
          ring_nf
          <;>
          omega
        
        apply h_main
        <;>
        simp_all
        <;>
        norm_num
        <;>
        linarith


    have h_step2 : (14 * n + 3) = 2 * (7 * n + 1) + 1 := by
        linarith
    --have gcd_step2 : Nat.gcd (14 * n + 3) (7 * n + 1) = Nat.gcd (7 * n + 1) 1  := by
        --simp_all only [gcd_self_add_left, gcd_mul_right_add_right, Nat.gcd_one_right, gcd_mul_right_add_left, gcd_add_self_right, Nat.gcd_one_left]
    ----have gcd_step3 : Nat.gcd (7 * n + 1) 1 = 1 := by
        ----try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
        ----
        --
    
    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


    
    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


    sorry



