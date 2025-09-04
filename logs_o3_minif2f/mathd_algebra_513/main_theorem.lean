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
  have h2 : b = 2 - a  := by
    linarith
  have h3 : 3 * a + 2 * (2 - a) = 5  := by
    linarith
  have h4 : a + 4 = 5  := by
    linarith
  have ha : a = 1  := by
    linarith
  have hb : b = 1  := by
    linarith
  exact ⟨ha, hb⟩