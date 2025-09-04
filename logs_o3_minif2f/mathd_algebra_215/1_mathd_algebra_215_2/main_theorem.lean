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

lemma mathd_algebra_215_2
  (S : Finset ℝ)
  (h₀ : ∀ (x : ℝ), x ∈ S ↔ (x + (3 : ℝ)) ^ (2 : ℕ) = (121 : ℝ))
  (cases_eq : ∀ (x : ℝ), (x + (3 : ℝ)) ^ (2 : ℕ) = (121 : ℝ) → x + (3 : ℝ) = (11 : ℝ) ∨ x + (3 : ℝ) = (-11 : ℝ))
  (candidate_values : ∀ (x : ℝ), (9 : ℝ) + x * (6 : ℝ) + x ^ (2 : ℕ) = (121 : ℝ) → x = (8 : ℝ) ∨ x = (-14 : ℝ)) :
  S = {(8 : ℝ), (-14 : ℝ)} := by
  have h₁ : S = {(8 : ℝ), (-14 : ℝ)} := by
    apply Finset.ext
    intro x
    simp only [Finset.mem_insert, Finset.mem_singleton, h₀]
    constructor
    · -- Prove the forward direction: if x ∈ S, then x = 8 or x = -14
      intro h
      have h₂ : (x + 3) ^ 2 = 121 := by simpa using h
      have h₃ : x + 3 = 11 ∨ x + 3 = -11 := by
        have h₄ : x + 3 = 11 ∨ x + 3 = -11 := by
          apply or_iff_not_imp_left.mpr
          intro h₅
          apply eq_of_sub_eq_zero
          apply mul_left_cancel₀ (sub_ne_zero.mpr h₅)
          nlinarith
        exact h₄
      cases h₃ with
      | inl h₃ =>
        have h₄ : x = 8 := by linarith
        simp [h₄]
      | inr h₃ =>
        have h₄ : x = -14 := by linarith
        simp [h₄]
    · -- Prove the reverse direction: if x = 8 or x = -14, then x ∈ S
      intro h
      cases h with
      | inl h =>
        rw [h]
        norm_num
      | inr h =>
        rw [h]
        norm_num
  exact h₁
