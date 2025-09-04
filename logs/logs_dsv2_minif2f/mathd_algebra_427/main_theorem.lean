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
theorem mathd_algebra_427 (x y z : ℝ) (h₀ : 3 * x + y = 17) (h₁ : 5 * y + z = 14)
    (h₂ : 3 * x + 5 * z = 41) : x + y + z = 12 := by
    have h_x : x = 66 / 13 := by
        have h₃ : x = 66 / 13 := by
            ring_nf at h₀ h₁ h₂ ⊢
            nlinarith [sq_nonneg (x - 66 / 13), sq_nonneg (y - 23 / 13), sq_nonneg (z - 67 / 13)]
        exact h₃
    have h_y : y = 23 / 13 := by
        have h₃ : y = 23 / 13 := by
            have h₄ : 3 * x + y = 17  := by
        
                gcongr
            rw [h_x] at h₄
            ring_nf at h₄ ⊢
            nlinarith
        exact h₃
    have h_z : z = 67 / 13 := by
        have h₃ : z = 67 / 13 := by
            have h₄ : 5 * y + z = 14  := by
        
                gcongr
            rw [h_y] at h₄
            ring_nf at h₄ ⊢
            nlinarith
        exact h₃
    have h_sum : x + y + z = 12 := by
        rw [h_x, h_y, h_z]
        <;> norm_num
        <;> ring_nf
        <;> norm_num
        <;> linarith
    exact h_sum