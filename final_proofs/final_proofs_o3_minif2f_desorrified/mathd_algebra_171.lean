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
theorem mathd_algebra_171 (f : ℝ → ℝ) (h₀ : ∀ x, f x = 5 * x + 4) : f 1 = 9 := by
    have h1 : f 1 = 5 * 1 + 4  := by
        exact h₀ (1 : ℝ)
    have h2 : 5 * 1 = 5  := by
        linarith
    have h3 : f 1 = 5 + 4  := by
        linarith
    have h4 : 5 + 4 = 9  := by
        linarith
    linarith