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

lemma mathd_algebra_288_1
  (x y : ℝ)
  (n : NNReal)
  (h₀ : x < (0 : ℝ) ∧ y < (0 : ℝ))
  (h₁ : |y| = (6 : ℝ))
  (h₂ : √((x - (8 : ℝ)) ^ (2 : ℕ) + (y - (3 : ℝ)) ^ (2 : ℕ)) = (15 : ℝ))
  (h₃ : √(x ^ (2 : ℕ) + y ^ (2 : ℕ)) = √(↑n : ℝ)) :
  y = (-6 : ℝ) := by
  have h_y_value : y = -6 := by
    have h₄ : y = -6 := by
      have h₅ : y < 0 := h₀.2
      have h₆ : |y| = 6 := h₁
      have h₇ : y = -6 := by
        -- Use the property of absolute value to find y
        have h₈ : y ≤ 0 := by linarith
        have h₉ : |y| = -y := by
          simp [abs_of_nonpos, h₈]
        rw [h₉] at h₆
        have h₁₀ : -y = 6 := by linarith
        have h₁₁ : y = -6 := by linarith
        exact h₁₁
      exact h₇
    exact h₄
  exact h_y_value
