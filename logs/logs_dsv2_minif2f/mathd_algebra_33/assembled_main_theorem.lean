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
theorem mathd_algebra_33 (x y z : ℝ) (h₀ : x ≠ 0) (h₁ : 2 * x = 5 * y) (h₂ : 7 * y = 10 * z) :
    z / x = 7 / 25 := by
    have h_y : y = (2 * x) / 5 := by
        have h₃ : y = (2 * x) / 5 := by
            apply Eq.symm
            linarith
        exact h₃
    have h_z : z = (7 * x) / 25 := by
        have h₃ : z = (7 * x) / 25 := by
            have h₄ : 7 * y = 10 * z  := by
        
                gcongr
            rw [h_y] at h₄
            ring_nf at h₄ ⊢
            nlinarith
        exact h₃
    have h_main : z / x = 7 / 25 := by
        rw [h_z]
        have h₃ : x ≠ 0  := by
      
            exact h₀
        field_simp [h₃]
        <;> ring_nf
        <;> field_simp [h₃]
        <;> nlinarith
    rw [h_main]
    <;> norm_num