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

lemma mathd_algebra_756_1
  (a b : ℝ)
  (h₀ : (2 : ℝ) ^ a = (32 : ℝ))
  (h₁ : a ^ b = (125 : ℝ)) :
  a = (5 : ℝ) := by
  have h_main : a = (5 : ℝ) := by
    have h₂ : a = 5 := by
      -- Take the natural logarithm of both sides of the equation 2^a = 32
      have h₃ : Real.log ((2 : ℝ) ^ a) = Real.log (32) := by rw [h₀]
      -- Use the logarithm power rule to simplify the left side
      have h₄ : Real.log ((2 : ℝ) ^ a) = a * Real.log 2 := by
        rw [Real.log_rpow (by norm_num : (2 : ℝ) > 0)]
      -- Substitute the simplified left side back into the equation
      rw [h₄] at h₃
      -- Simplify the right side
      have h₅ : Real.log (32) = Real.log (2 ^ 5) := by norm_num
      rw [h₅] at h₃
      -- Use the logarithm power rule again
      have h₆ : Real.log (2 ^ 5) = 5 * Real.log 2 := by
        rw [Real.log_pow] <;> ring_nf <;> norm_num
      rw [h₆] at h₃
      -- Solve for a using basic arithmetic
      have h₇ : a * Real.log 2 = 5 * Real.log 2 := by linarith
      have h₈ : Real.log 2 ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
      have h₉ : a = 5 := by
        apply mul_left_cancel₀ h₈
        nlinarith
      exact h₉
    exact h₂
  exact h_main
