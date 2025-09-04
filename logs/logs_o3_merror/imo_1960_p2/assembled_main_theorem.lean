import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
import Mathlib
import Aesop
open Real
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
theorem imo_1960_p2 (x : ℝ) 
  (h₀ : 0 ≤ 1 + 2*x) 
  (h₁ : (1 - sqrt (1 + 2*x))^2 ≠ 0)
  (h₂ : 4*x^2/(1 - sqrt (1 + 2*x))^2 < 2*x + 9) 
  : -(1/2) ≤ x ∧ x < 45/8 := by
  try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
  sorry
