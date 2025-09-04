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
theorem mathd_numbertheory_150 (n : ℕ) (h₀ : ¬Nat.Prime (7 + 30 * n)) : 6 ≤ n := by 
    have prime0 : Nat.Prime (7 + 30 * 0)  := by
        decide -- 7 is prime
    have prime1 : Nat.Prime (7 + 30 * 1)  := by
        decide -- 37 is prime
    have prime2 : Nat.Prime (7 + 30 * 2)  := by
        decide -- 67 is prime
    have prime3 : Nat.Prime (7 + 30 * 3)  := by
        decide -- 97 is prime
    have prime4 : Nat.Prime (7 + 30 * 4)  := by
        decide -- 127 is prime
    have prime5 : Nat.Prime (7 + 30 * 5)  := by
        decide -- 157 is prime
    by_cases h : n < 6
    · -- In the case n < 6, we examine all possibilities.
    
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
        sorry
    · -- Step 3: If n is not less than 6, then n ≥ 6 by definition.
        exact Nat.le_of_not_lt h