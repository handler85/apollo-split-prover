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
theorem mathd_algebra_400 (x : ℝ) (h₀ : 5 + 500 / 100 * 10 = 110 / 100 * x) : x = 50 := by
  have h₁ : x = 50 := by
    ring_nf at h₀ ⊢
    nlinarith
    <;>
    (try norm_num at h₀ ⊢)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf at h₀ ⊢)
    <;>
    (try nlinarith)
  exact h₁