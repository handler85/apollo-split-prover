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
  have h2 : t = 3 * (9 - 2 * t) + 1 := by
    linarith
  have h3 : t = 3 * 9 - 3 * (2 * t) + 1 := by
    linarith
  have h4 : t = 27 - 6 * t + 1 := by
    linarith
  have h5 : t = 28 - 6 * t := by
    linarith
  have h6 : 7 * t = 28 := by
    linarith
  have ht4 : t = 4 := by
    linarith
  have hs1 : s = 9 - 2 * 4 := by
    linarith
  have hs1' : s = 1 := by
    linarith
  exact And.intro hs1' ht4