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

lemma algebra_amgm_sum1toneqn_prod1tonleq1_3
  (a : ℕ → NNReal)
  (n : ℕ)
  (h₀ : ∑ x ∈ Finset.range n, a x = (↑n : NNReal))
  (substituted : (∏ x ∈ Finset.range n, a x) ^ ((1 : ℕ) / n) ≤ (↑n : NNReal) / (↑n : NNReal))
  (simplification : n / n = (1 : ℕ)) :
  (∏ x ∈ Finset.range n, a x) ^ ((1 : ℕ) / n) ≤ (1 : NNReal) := by
  have h_main : (∏ x ∈ Finset.range n, a x) ^ ((1 : ℕ) / n) ≤ (1 : NNReal) := by
    have h₁ : (n : NNReal) / (n : NNReal) = 1 := by
      by_cases h : n = 0
      · simp [h]
        <;>
        aesop
      · field_simp [h]
        <;>
        aesop
    have h₂ : (∏ x ∈ Finset.range n, a x) ^ ((1 : ℕ) / n) ≤ (↑n : NNReal) / (↑n : NNReal) := substituted
    have h₃ : (↑n : NNReal) / (↑n : NNReal) = 1 := by
      by_cases h : n = 0
      · simp [h]
        <;>
        aesop
      · field_simp [h]
        <;>
        aesop
    calc
      (∏ x ∈ Finset.range n, a x) ^ ((1 : ℕ) / n) ≤ (↑n : NNReal) / (↑n : NNReal) := h₂
      _ = 1 := by simp [h₃]
      _ ≤ (1 : NNReal) := by simp
  exact h_main
