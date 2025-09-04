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
theorem mathd_algebra_215 (S : Finset ℝ) (h₀ : ∀ x : ℝ, x ∈ S ↔ (x + 3) ^ 2 = 121) :
    (∑ k in S, k) = -6 := by
  have h₁ : S = {8, -14} := by
    apply Finset.ext
    intro x
    simp only [Finset.mem_insert, Finset.mem_singleton, h₀]
    constructor
    · intro h
      have h₁ : (x + 3) ^ 2 = 121  := by
        simpa using h
      have h₂ : x + 3 = 11 ∨ x + 3 = -11 := by
        apply or_iff_not_imp_left.mpr
        intro h₃
        apply eq_of_sub_eq_zero
        apply mul_left_cancel₀ (sub_ne_zero.mpr h₃)
        nlinarith
      cases h₂ with
      | inl h₂ =>
        have h₃ : x = 8  := by
          linarith
        simp [h₃]
        <;> norm_num
      | inr h₂ =>
        have h₃ : x = -14  := by
          linarith
        simp [h₃]
        <;> norm_num
    · intro h
      have h₁ : x = 8 ∨ x = -14  := by
        simpa using h
      cases h₁ with
      | inl h₁ =>
        rw [h₁]
        norm_num
      | inr h₁ =>
        rw [h₁]
        norm_num
  have h₂ : (∑ k in S, k) = -6 := by
    rw [h₁]
    norm_num
    <;>
    simp [Finset.sum_pair (show (8 : ℝ) ≠ -14 by norm_num)]
    <;>
    norm_num
    <;>
    linarith
  exact h₂