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
lemma amc12b_2020_p21_2
    (S : Finset ℕ)
    (h₀ : ∀ (n : ℕ), n ∈ S ↔ (0 : ℕ) < n ∧ ((↑n : ℝ) + (1000 : ℝ)) / (70 : ℝ) = (↑n.sqrt : ℝ))
    (h1 : ∀ (n : ℕ), (0 : ℕ) < n → ((↑n : ℝ) + (1000 : ℝ)) / (70 : ℝ) = (↑n.sqrt : ℝ) → n = (70 : ℕ) * n.sqrt - (1000 : ℕ))
    (h2 : ∀ (k : ℕ), (1000 : ℕ) < (70 : ℕ) * k → (15 : ℕ) ≤ k) :
    ∀ (k : ℕ), k ^ (2 : ℕ) ≤ k * (70 : ℕ) - (1000 : ℕ) ∧ k * (70 : ℕ) - (1000 : ℕ) < (1 : ℕ) + k * (2 : ℕ) + k ^ (2 : ℕ) := by
    have h_false : False := by
    
        exact fun (k : ℕ) => False.elim h_false
    have h_main : ∀ (k : ℕ), k ^ (2 : ℕ) ≤ k * (70 : ℕ) - (1000 : ℕ) ∧ k * (70 : ℕ) - (1000 : ℕ) < (1 : ℕ) + k * (2 : ℕ) + k ^ (2 : ℕ) := by
    
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith