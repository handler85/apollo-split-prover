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

lemma amc12a_2021_p18_1
  (f : ℚ → ℝ)
  (h₀ : ∀ (x : ℚ), (0 : ℚ) < x → ∀ (y : ℚ), (0 : ℚ) < y → f (x * y) = f x + f y)
  (h₁ : ∀ (p : ℕ), Nat.Prime p → f (↑p : ℚ) = (↑p : ℝ)) :
  f (1 : ℚ) = (0 : ℝ) := by
  have h_main : f (1 : ℚ) = (0 : ℝ) := by
    have h₂ : f ((1 : ℚ) * (1 : ℚ)) = f (1 : ℚ) + f (1 : ℚ) := by
      have h₃ := h₀ (1 : ℚ) (by norm_num) (1 : ℚ) (by norm_num)
      simpa using h₃
    have h₄ : f ((1 : ℚ) * (1 : ℚ)) = f (1 : ℚ) := by
      norm_num
    have h₅ : f (1 : ℚ) + f (1 : ℚ) = f (1 : ℚ) := by linarith
    have h₆ : f (1 : ℚ) = 0 := by linarith
    exact h₆
  exact h_main
