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
theorem mathd_numbertheory_175 : 2 ^ 2010 % 10 = 4 := by
    have units_digit_cycle : ∀ n : ℕ, 2^(n+4) % 10 = 2^n % 10 := by
        intro
    have mod_cycle : 2010 % 4 = 2 := by
        omega
    have reduction : 2^(2010) % 10 = 2^(2010 % 4) % 10 := by
        omega
    have base_case : 2^2 % 10 = 4 := by
        linarith
    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
    
