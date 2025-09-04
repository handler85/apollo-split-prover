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
lemma algebra_amgm_sum1toneqn_prod1tonleq1_4
    (a : ℕ → NNReal)
    (n : ℕ)
    (h₀ : ∑ x ∈ Finset.range n, a x = (↑n : NNReal))
    (substituted : (∏ x ∈ Finset.range n, a x) ^ ((1 : ℕ) / n) ≤ (↑n : NNReal) / (↑n : NNReal))
    (simplification : n / n = (1 : ℕ))
    (geo_mean_bound : (∏ x ∈ Finset.range n, a x) ^ ((1 : ℕ) / n) ≤ (1 : NNReal)) :
    (∏ x ∈ Finset.range n, a x) ^ ((1 : ℕ) / n * n) ≤ (1 : NNReal) := by
    have h_main : (∏ x ∈ Finset.range n, a x) ^ ((1 : ℕ) / n * n) ≤ (1 : NNReal) := by
        have h₁ : (∏ x ∈ Finset.range n, a x) ^ ((1 : ℕ) / n * n) = ((∏ x ∈ Finset.range n, a x) ^ ((1 : ℕ) / n)) ^ n := by
            rw [← pow_mul]
            <;> simp [mul_comm]
            <;> ring_nf
        rw [h₁]
        have h₂ : ((∏ x ∈ Finset.range n, a x) ^ ((1 : ℕ) / n)) ^ n ≤ (1 : NNReal) ^ n := by
            have h₃ : (∏ x ∈ Finset.range n, a x) ^ ((1 : ℕ) / n) ≤ (1 : NNReal) := by
                simpa [NNReal.coe_one] using geo_mean_bound
      
            gcongr
        have h₃ : (1 : NNReal) ^ n = (1 : NNReal)  := by
            simp
        rw [h₃] at h₂
        exact h₂
    exact h_main