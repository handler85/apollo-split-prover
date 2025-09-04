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
lemma mathd_algebra_80_1
    (x : ℝ)
    (h₀ : ¬x = (-1 : ℝ))
    (h₁ : x * ((1 : ℝ) + x)⁻¹ - ((1 : ℝ) + x)⁻¹ * (9 : ℝ) = (2 : ℝ)) :
    (-9 : ℝ) + x = (2 : ℝ) + x * (2 : ℝ) := by
    have h₂ : x = -11 := by
        have h₃ : (1 + x) ≠ 0 := by
            intro h
            apply h₀
            linarith
        field_simp [h₃] at h₁
        ring_nf at h₁
        apply mul_left_cancel₀ (sub_ne_zero.mpr h₃)
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
        sorry
    have h₃ : (-9 : ℝ) + x = (2 : ℝ) + x * (2 : ℝ) := by
        rw [h₂]
        norm_num
        <;>
        linarith
    exact h₃