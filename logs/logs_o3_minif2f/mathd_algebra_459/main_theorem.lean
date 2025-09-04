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
theorem mathd_algebra_459 (a b c d : ℚ) 
  (h₀ : 3 * a = b + c + d) 
  (h₁ : 4 * b = a + c + d)
  (h₂ : 2 * c = a + b + d) 
  (h₃ : 8 * a + 10 * b + 6 * c = 24) : ↑d.den + d.num = 28 := by
  have d_eq1 : d = 3 * a - b - c := by
    linarith
  have d_eq2 : d = 4 * b - a - c := by
    linarith
  have eq1 : 3 * a - b - c = 4 * b - a - c := by
    linarith
  have rel1 : 4 * a = 5 * b := by
    linarith
  have d_eq3 : d = 2 * c - a - b := by
    linarith
  have eq2 : 3 * a - b - c = 2 * c - a - b := by
    linarith
  have rel2 : 4 * a = 3 * c := by
    linarith
  have b_expr : b = (4 * a) / 5 := by
    linarith
  have c_expr : c = (4 * a) / 3 := by
    linarith
  have a_eq : a = 1 := by
    linarith
  have b_val : b = 4 / 5 := by
    linarith
  have c_val : c = 4 / 3 := by
    linarith
  have d_val : d = 3 - (4 / 5) - (4 / 3) := by
    linarith
  have d_simpl : d = 13 / 15 := by
    linarith
  have final : ↑d.den + d.num = 28 := by
    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
    sorry
  exact final