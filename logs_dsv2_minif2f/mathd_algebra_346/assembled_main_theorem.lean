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
theorem mathd_algebra_346 (f g : ℝ → ℝ) (h₀ : ∀ x, f x = 2 * x - 3) (h₁ : ∀ x, g x = x + 1) :
    g (f 5 - 1) = 7 := by
    have h_f5 : f 5 = 7 := by
        have h₂ : f 5 = 2 * (5 : ℝ) - 3  := by
            rw [h₀]
        rw [h₂]
        norm_num
        <;>
        linarith
    have h_f5_minus_1 : f 5 - 1 = 6 := by
        have h₂ : f 5 = 7  := by
      
            gcongr
        rw [h₂]
        <;> norm_num
        <;> linarith
    have h_g : g (f 5 - 1) = 7 := by
        have h₃ : f 5 - 1 = 6  := by
      
            gcongr
        have h₄ : g (f 5 - 1) = g 6  := by
            rw [h₃]
        rw [h₄]
        have h₅ : g 6 = 6 + 1 := by
            have h₅₁ : g 6 = 6 + 1 := by
                rw [h₁]
                <;> norm_num
            exact h₅₁
        rw [h₅]
        <;> norm_num
        <;> linarith
    rw [h_g]
    <;> norm_num
    <;> linarith