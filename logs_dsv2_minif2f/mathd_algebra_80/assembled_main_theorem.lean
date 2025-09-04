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
theorem mathd_algebra_80 (x : ℝ) (h₀ : x ≠ -1) (h₁ : (x - 9) / (x + 1) = 2) : x = -11 := by
  have h₂ : x = -11 := by
    have h₃ : x + 1 ≠ 0 := by
      intro h
      apply h₀
      linarith
    field_simp [h₃] at h₁
    ring_nf at h₁
    apply Eq.symm
    nlinarith [sq_pos_of_ne_zero (sub_ne_zero_of_ne h₀)]
  exact h₂