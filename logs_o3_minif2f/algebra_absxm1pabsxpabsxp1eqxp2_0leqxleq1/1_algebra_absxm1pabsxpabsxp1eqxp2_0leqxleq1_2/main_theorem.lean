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

lemma algebra_absxm1pabsxpabsxp1eqxp2_0leqxleq1_2
  (x : ℝ)
  (h₀ : |x - (1 : ℝ)| + |x| + |x + (1 : ℝ)| = x + (2 : ℝ))
  (h_nonneg : (0 : ℝ) ≤ x) :
  x ≤ (1 : ℝ) := by
  have h_main : x ≤ 1 := by
    by_contra h
    -- Assume x > 1
    have h₁ : x > 1 := by linarith
    -- Calculate the absolute values under the assumption x > 1
    have h₂ : |x - 1| = x - 1 := by
      rw [abs_of_nonneg] <;> linarith
    have h₃ : |x| = x := by
      rw [abs_of_nonneg] <;> linarith
    have h₄ : |x + 1| = x + 1 := by
      rw [abs_of_nonneg] <;> linarith
    -- Substitute the absolute values into the original equation
    rw [h₂, h₃, h₄] at h₀
    -- Simplify the equation to find a contradiction
    nlinarith [sq_nonneg (x - 1), sq_nonneg (x - 2), sq_nonneg (x + 1)]
  exact h_main
