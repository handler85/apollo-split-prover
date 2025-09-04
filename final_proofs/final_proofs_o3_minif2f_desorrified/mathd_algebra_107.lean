import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
/- Find the radius of the circle with equation x² + 8x + y² – 6y = 0.
    Show that after completing the square, (x + 4)² + (y – 3)² = 5². –/
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
theorem mathd_algebra_107 (x y : ℝ) (h₀ : x² + 8 * x + y² - 6 * y = 0) :
    (x + 4)² + (y - 3)² = 5² := by
  try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
  
