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
theorem mathd_numbertheory_728 : (29 ^ 13 - 5 ^ 13) % 7 = 3 := by
    have h1 : 29 % 7 = 1  := by
        omega
    have h2 : (29 ^ 13) % 7 = (1 ^ 13) % 7  := by
        omega
    have h3 : 5 ^ 6 % 7 = 1  := by
        omega
    have h4 : (5 ^ 13) % 7 = ((5 ^ 6) ^ 2 * 5) % 7  := by
        omega
    have h5 : ((5 ^ 6) ^ 2) % 7 = 1 ^ 2 % 7  := by
        omega
    have h6 : 1 ^ 2 % 7 = 1  := by
        omega
    have h7 : (5 ^ 13) % 7 = (1 * 5) % 7  := by
        omega
    have h8 : (1 * 5) % 7 = 5  := by
        omega
    have h9 : (29 ^ 13 - 5 ^ 13) % 7 = (1 - 5) % 7  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
        sorry

    have h10 : (1 - 5) % 7 = (-4) % 7  := by
        omega
    have h11 : (-4) % 7 = 3  := by
        omega
    omega