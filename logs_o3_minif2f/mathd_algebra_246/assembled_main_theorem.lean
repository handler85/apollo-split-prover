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
theorem mathd_algebra_246 (a b : ℝ) (f : ℝ → ℝ)
    (h₀ : ∀ x, f x = a * x ^ 4 - b * x ^ 2 + x + 5)
    (h₂ : f (-3) = 2) : f 3 = 8 := by
    have h1 : f (-3) = a * (-3) ^ 4 - b * (-3) ^ 2 + (-3) + 5  := by
        exact h₀ (-3 : ℝ)
    have h2 : f (-3) = 81 * a - 9 * b - 3 + 5  := by
        linarith
    have h3 : f (-3) = 81 * a - 9 * b + 2  := by
        linarith
    have h4 : 81 * a - 9 * b + 2 = 2  := by
    
        linarith
    have h5 : 81 * a - 9 * b = 0  := by
        linarith
    have h6 : 9 * (9 * a - b) = 0  := by
        linarith
    have h7 : b = 9 * a  := by
        linarith
    have h8 : f 3 = a * 3 ^ 4 - b * 3 ^ 2 + 3 + 5  := by
        exact h₀ (3 : ℝ)
    have h9 : f 3 = 81 * a - 9 * b + 8  := by
        linarith
    have h10 : f 3 = 81 * a - 9 * (9 * a) + 8  := by
        linarith
    have h11 : f 3 = 8  := by
        linarith
    exact h11