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
theorem mathd_algebra_338 (a b c : ℝ) (h₀ : 3 * a + b + c = -3) (h₁ : a + 3 * b + c = 9)
    (h₂ : a + b + 3 * c = 19) : a * b * c = -56 := by
    have h_b : b = a + 6 := by
        have h₃ : -2 * a + 2 * b = 12 := by
            linarith
        have h₄ : -a + b = 6  := by
            linarith
        linarith
    have h_c : c = a + 11 := by
        have h₃ : -2 * a + 2 * c = 22 := by
            linarith
        have h₄ : -a + c = 11  := by
            linarith
        linarith
    have h_a : a = -4 := by
        have h₃ : 3 * a + b + c = -3  := by
      
            gcongr
        rw [h_b, h_c] at h₃
        ring_nf at h₃
        linarith
    have h_main : a * b * c = -56 := by
        rw [h_a] at h_b h_c ⊢
        simp [h_b, h_c]
        <;> ring_nf
        <;> nlinarith
    exact h_main