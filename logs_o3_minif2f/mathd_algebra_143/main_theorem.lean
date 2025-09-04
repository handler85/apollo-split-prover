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
theorem mathd_algebra_143 (f g : ℝ → ℝ) (h₀ : ∀ x, f x = x + 1) (h₁ : ∀ x, g x = x ^ 2 + 3) :
    f (g 2) = 8 := by 
    have h_g_def : g 2 = 2 ^ 2 + 3  := by
        exact h₁ (2 : ℝ)
    have h_squared : 2 ^ 2 + 3 = 4 + 3  := by
        linarith
    have h_sum : 4 + 3 = 7  := by
        linarith
    have h_g2 : g 2 = 7  := by
        linarith
    have h_f_def : f 7 = 7 + 1  := by
        exact h₀ (7 : ℝ)
    have h_addition : 7 + 1 = 8  := by
        linarith
    have h_f7 : f 7 = 8  := by
        linarith
    have h_subst : f (g 2) = f 7  := by
        rw [h_g2]
    linarith