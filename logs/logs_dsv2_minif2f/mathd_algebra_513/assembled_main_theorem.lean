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
theorem mathd_algebra_513 (a b : ℝ) (h₀ : 3 * a + 2 * b = 5) (h₁ : a + b = 2) : a = 1 ∧ b = 1 := by
    have h_b : b = 1 := by
        have h₂ : a = 2 - b := by
            linarith
        rw [h₂] at h₀
        linarith
    have h_a : a = 1 := by
        have h₃ : a = 1 := by
            have h₄ : a + b = 2  := by
        
                gcongr
            rw [h_b] at h₄
            linarith
        exact h₃
    have h_main : a = 1 ∧ b = 1 := by
        exact ⟨h_a, h_b⟩
    exact h_main