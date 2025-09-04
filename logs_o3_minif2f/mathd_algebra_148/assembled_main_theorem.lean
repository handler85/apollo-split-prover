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
theorem mathd_algebra_148 (c : ℝ) (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = c * x ^ 3 - 9 * x + 3)
  (h₁ : f 2 = 9) : c = 3 := by 
  have step1 : f 2 = c * (2 ^ 3) - 9 * 2 + 3 := by
    exact h₀ (2 : ℝ)
  have step2 : f 2 = 8 * c - 9 * 2 + 3 := by
    linarith
  have step3 : f 2 = 8 * c - 18 + 3 := by
    linarith
  have step4 : f 2 = 8 * c - 15 := by
    linarith
  have step5 : 8 * c - 15 = 9 := by
    linarith
  have step6 : 8 * c = 9 + 15 := by
    linarith
  have step7 : 8 * c = 24 := by
    linarith
  have step8 : c = 3 := by
    linarith
  exact step8