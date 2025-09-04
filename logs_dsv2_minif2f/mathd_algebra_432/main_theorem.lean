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
theorem mathd_algebra_432 (x : ℝ) : (x + 3) * (2 * x - 6) = 2 * x ^ 2 - 18 := by
  have h_main : (x + 3) * (2 * x - 6) = 2 * x ^ 2 - 18 := by
    ring_nf
    <;>
    (try norm_num) <;>
    (try linarith) <;>
    (try nlinarith) <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    nlinarith
  rw [h_main]
  <;>
  nlinarith