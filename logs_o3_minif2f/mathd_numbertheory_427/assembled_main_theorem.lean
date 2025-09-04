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
theorem mathd_numbertheory_427 (a : ℕ) (h₀ : a = ∑ k in Nat.divisors 500, k) :
    (∑ k in Finset.filter (fun x => Nat.Prime x) (Nat.divisors a), k) = 25 := by
    have h1 : 500 = 2^2 * 5^3  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
    have h2 : ∑ k in Nat.divisors 500, k = ((2^(2+1) - 1) / (2 - 1)) * ((5^(3+1) - 1) / (5 - 1))  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
    have h3 : ((2^(2+1) - 1) / (2 - 1)) * ((5^(3+1) - 1) / (5 - 1)) = 7 * 156  := by
        linarith
    have h4 : 7 * 156 = 1092  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
    have h_a : a = 1092  := by
        decide
    have h5 : 1092 = 2^2 * 3 * 7 * 13  := by
        omega
    have h6 : Finset.filter (fun x => Nat.Prime x) (Nat.divisors 1092) = {2, 3, 7, 13}  := by
        linarith
    have h7 : (∑ k in {2, 3, 7, 13}, k) = 25  := by
        linarith
    linarithdecide