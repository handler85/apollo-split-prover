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

lemma mathd_algebra_196_1
  (S : Finset ℝ)
  (h₀ : ∀ (x : ℝ), x ∈ S ↔ |(2 : ℝ) - x| = (3 : ℝ))
  (h_5_in_S : |(-3 : ℝ)| = (3 : ℝ))
  (h_neg1_in_S : |(3 : ℝ)| = (3 : ℝ)) :
  S ⊆ {(-1 : ℝ), (5 : ℝ)} := by
  have h₁ : S ⊆ {(-1 : ℝ), (5 : ℝ)} := by
    intro x hx
    have h₂ : x ∈ S := hx
    have h₃ : |(2 : ℝ) - x| = (3 : ℝ) := (h₀ x).mp h₂
    have h₄ : x = -1 ∨ x = 5 := by
      have h₅ : |(2 : ℝ) - x| = (3 : ℝ) := h₃
      have h₆ : (2 : ℝ) - x = 3 ∨ (2 : ℝ) - x = -3 := by
        apply eq_or_eq_neg_of_abs_eq
        <;> linarith
      cases h₆ with
      | inl h₆ =>
        have h₇ : (2 : ℝ) - x = 3 := h₆
        have h₈ : x = -1 := by linarith
        exact Or.inl h₈
      | inr h₆ =>
        have h₇ : (2 : ℝ) - x = -3 := h₆
        have h₈ : x = 5 := by linarith
        exact Or.inr h₈
    cases h₄ with
    | inl h₄ =>
      have h₅ : x = -1 := h₄
      have h₆ : x ∈ ({(-1 : ℝ), (5 : ℝ)} : Finset ℝ) := by
        rw [h₅]
        simp
        <;> norm_num
      exact h₆
    | inr h₄ =>
      have h₅ : x = 5 := h₄
      have h₆ : x ∈ ({(-1 : ℝ), (5 : ℝ)} : Finset ℝ) := by
        rw [h₅]
        simp
        <;> norm_num
      exact h₆
  exact h₁
