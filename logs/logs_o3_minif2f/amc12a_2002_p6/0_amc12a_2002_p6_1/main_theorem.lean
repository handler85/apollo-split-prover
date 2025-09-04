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

lemma amc12a_2002_p6_1
  (n : ℕ)
  (h₀ : (0 : ℕ) < n)
  (m : ℕ := n + (1 : ℕ))
  (p : ℕ := (1 : ℕ))
  (hm : n < m) :
  ∃ (m : ℕ), n < m ∧ ∃ (p : ℕ), m * p ≤ m + p := by
  have h_main : ∃ (m : ℕ), n < m ∧ ∃ (p : ℕ), m * p ≤ m + p := by
    refine' ⟨n + 1, by
      -- Prove that n < n + 1
      linarith [h₀], 1, _⟩
    -- Prove that (n + 1) * 1 ≤ (n + 1) + 1
    simp [Nat.mul_comm, Nat.add_assoc]
    <;>
    ring_nf
    <;>
    omega
  
  exact h_main
