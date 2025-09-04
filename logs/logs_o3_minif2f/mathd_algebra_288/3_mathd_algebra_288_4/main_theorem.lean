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

lemma mathd_algebra_288_4
  (x y : ℝ)
  (n : NNReal)
  (h₀ : x < (0 : ℝ))
  (hy : y = (-6 : ℝ))
  (x_sq_eq : (64 : ℝ) - x * (16 : ℝ) + x ^ (2 : ℕ) = (144 : ℝ))
  (sq_eq h2_simpl : True)
  (h₃ : √((36 : ℝ) + x ^ (2 : ℕ)) = √(↑n : ℝ))
  (h₂ : True) :
  x = (-4 : ℝ) := by
  have h_main : x = (-4 : ℝ) := by
    have h₄ : x ^ 2 - 16 * x - 80 = 0 := by
      have h₅ : (64 : ℝ) - x * (16 : ℝ) + x ^ (2 : ℕ) = (144 : ℝ) := x_sq_eq
      ring_nf at h₅ ⊢
      nlinarith
    have h₅ : x = (-4 : ℝ) ∨ x = 20 := by
      have h₆ : x ^ 2 - 16 * x - 80 = 0 := h₄
      have h₇ : x = (-4 : ℝ) ∨ x = 20 := by
        have h₈ : (x - 20) * (x + 4) = 0 := by
          nlinarith
        have h₉ : x - 20 = 0 ∨ x + 4 = 0 := by
          apply eq_zero_or_eq_zero_of_mul_eq_zero h₈
        cases h₉ with
        | inl h₉ =>
          have h₁₀ : x - 20 = 0 := h₉
          have h₁₁ : x = 20 := by linarith
          exact Or.inr h₁₁
        | inr h₉ =>
          have h₁₀ : x + 4 = 0 := h₉
          have h₁₁ : x = -4 := by linarith
          exact Or.inl h₁₁
      exact h₇
    cases h₅ with
    | inl h₅ =>
      exact h₅
    | inr h₅ =>
      have h₆ : x < (0 : ℝ) := h₀
      have h₇ : x = 20 := h₅
      linarith
  exact h_main
