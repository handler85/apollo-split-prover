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
theorem mathd_algebra_148 (c : ℝ) (f : ℝ → ℝ) (h₀ : ∀ x, f x = c * x ^ 3 - 9 * x + 3)
    (h₁ : f 2 = 9) : c = 3 := by
    have h₂ : c = 3 := by
        have h₃ : f 2 = 9  := by
      
            gcongr
        have h₄ : f 2 = c * (2 : ℝ) ^ 3 - 9 * (2 : ℝ) + 3 := by
            rw [h₀]
            <;> ring
        rw [h₄] at h₃
        norm_num at h₃ ⊢
        <;> linarith
    exact h₂