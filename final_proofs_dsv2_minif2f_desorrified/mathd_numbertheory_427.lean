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
    have h₁ : a = 1092 := by
        rw [h₀]
        rw [show (500 : ℕ) = 2 ^ 2 * 5 ^ 3 by norm_num]
        rw [Nat.divisors_mul, Nat.divisors_prime_pow (by decide : Nat.Prime 2), Nat.divisors_prime_pow (by decide : Nat.Prime 5)]
        <;> norm_num
        <;> rfl
        <;> decide
    have h₂ : (∑ k in Finset.filter (fun x => Nat.Prime x) (Nat.divisors a), k) = 25 := by
        rw [h₁]
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
        

    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarithgcongr
    
