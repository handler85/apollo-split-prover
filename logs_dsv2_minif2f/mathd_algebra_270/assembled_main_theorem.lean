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
theorem mathd_algebra_270 (f : ℝ → ℝ) (h₀ : ∀ (x) (_ : x ≠ -2), f x = 1 / (x + 2)) :
    f (f 1) = 3 / 7 := by
  have h1 : f 1 = 1 / 3 := by
    have h1_1 : f 1 = 1 / (1 + 2 : ℝ) := by
      apply h₀
      norm_num
    rw [h1_1]
    <;> norm_num
  have h2 : f (f 1) = 3 / 7 := by
    rw [h1]
    have h2_1 : f (1 / 3 : ℝ) = 1 / ((1 / 3 : ℝ) + 2) := by
      apply h₀
      norm_num
    rw [h2_1]
    <;> norm_num
    <;> field_simp
    <;> ring
    <;> norm_num
  rw [h2]
  <;> norm_num