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
theorem mathd_algebra_246 (a b : ℝ) (f : ℝ → ℝ) (h₀ : ∀ x, f x = a * x ^ 4 - b * x ^ 2 + x + 5)
    (h₂ : f (-3) = 2) : f 3 = 8 := by
    have h_b_eq : b = 9 * a := by
        have h₃ : f (-3) = 2  := by
      
            gcongr
        have h₄ : f (-3) = a * (-3 : ℝ) ^ 4 - b * (-3 : ℝ) ^ 2 + (-3 : ℝ) + 5 := by
            rw [h₀]
            <;> ring_nf
        rw [h₄] at h₃
        ring_nf at h₃
        linarith
    have h_f3 : f 3 = 8 := by
        have h₃ : f 3 = a * (3 : ℝ) ^ 4 - b * (3 : ℝ) ^ 2 + (3 : ℝ) + 5 := by
            rw [h₀]
            <;> ring_nf
        rw [h₃]
        rw [h_b_eq]
        ring_nf
        <;> nlinarith
    exact h_f3