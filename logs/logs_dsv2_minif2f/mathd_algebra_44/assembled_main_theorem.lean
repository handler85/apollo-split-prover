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
theorem mathd_algebra_44 (s t : ℝ) (h₀ : s = 9 - 2 * t) (h₁ : t = 3 * s + 1) : s = 1 ∧ t = 4 := by
    have h_t : t = 4 := by
        have h₂ : t = 4 := by
            have h₃ : t = 3 * s + 1  := by
        
                gcongr
            have h₄ : s = 9 - 2 * t  := by
        
                gcongr
            rw [h₄] at h₃
            ring_nf at h₃ ⊢
            nlinarith
        exact h₂
    have h_s : s = 1 := by
        have h₂ : s = 1 := by
            have h₃ : s = 9 - 2 * t  := by
        
                gcongr
            have h₄ : t = 4  := by
        
                gcongr
            rw [h₄] at h₃
            linarith
        exact h₂
    have h_final : s = 1 ∧ t = 4 := by
        exact ⟨h_s, h_t⟩
    exact h_final