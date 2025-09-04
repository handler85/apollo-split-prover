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
theorem amc12a_2002_p6 (n : ℕ) (h₀ : 0 < n) : ∃ m, m > n ∧ ∃ p, m * p ≤ m + p := by
  have h_main : ∃ m, m > n ∧ ∃ p, m * p ≤ m + p := by
    use n + 1
    constructor
    · -- Prove that n + 1 > n
      linarith
    · -- Prove that there exists a p such that (n + 1) * p ≤ (n + 1) + p
      use 1
      <;> simp [mul_comm, mul_one, Nat.mul_add, Nat.add_mul]
      <;> ring_nf
      <;> omega
  exact h_main