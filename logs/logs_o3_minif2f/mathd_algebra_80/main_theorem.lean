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
theorem mathd_algebra_80 (x : ℝ) (h₀ : x ≠ -1) (h₁ : (x - 9) / (x + 1) = 2) : x = -11 := by
  have step1 : x - 9 = 2 * (x + 1) := by
    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
    sorry
  have step2 : x - 9 = 2*x + 2 := by
    linarith
  have step3 : -9 = x + 2 := by
    linarith
  have step4 : x = -11 := by
    linarith
  exact step4