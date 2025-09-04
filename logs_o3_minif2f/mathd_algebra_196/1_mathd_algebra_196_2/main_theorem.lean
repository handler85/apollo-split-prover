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

lemma mathd_algebra_196_2
  (S : Finset ℝ)
  (h₀ : ∀ (x : ℝ), x ∈ S ↔ |(2 : ℝ) - x| = (3 : ℝ))
  (h_S_subset : S ⊆ {(-1 : ℝ), (5 : ℝ)})
  (h_5_in_S : |(-3 : ℝ)| = (3 : ℝ))
  (h_neg1_in_S : |(3 : ℝ)| = (3 : ℝ)) :
  S = {(-1 : ℝ), (5 : ℝ)} := by
  have h_main : S = {(-1 : ℝ), (5 : ℝ)} := by
    apply Finset.ext
    intro x
    simp only [Finset.mem_insert, Finset.mem_singleton, h₀]
    constructor
    · -- Prove the forward direction: if |2 - x| = 3, then x = -1 or x = 5
      intro h
      have h₁ : |(2 : ℝ) - x| = 3 := by simpa using h
      have h₂ : (2 : ℝ) - x = 3 ∨ (2 : ℝ) - x = -3 := by
        apply eq_or_eq_neg_of_abs_eq
        <;> linarith
      cases h₂ with
      | inl h₂ =>
        have h₃ : x = -1 := by linarith
        simp_all
        <;> norm_num
      | inr h₂ =>
        have h₃ : x = 5 := by linarith
        simp_all
        <;> norm_num
    · -- Prove the reverse direction: if x = -1 or x = 5, then |2 - x| = 3
      intro h
      cases h with
      | inl h =>
        rw [h]
        norm_num [abs_of_nonneg, abs_of_nonpos]
        <;>
        simp_all [abs_of_nonneg, abs_of_nonpos]
        <;>
        norm_num
        <;>
        linarith
      | inr h =>
        rw [h]
        norm_num [abs_of_nonneg, abs_of_nonpos]
        <;>
        simp_all [abs_of_nonneg, abs_of_nonpos]
        <;>
        norm_num
        <;>
        linarith
  exact h_main
