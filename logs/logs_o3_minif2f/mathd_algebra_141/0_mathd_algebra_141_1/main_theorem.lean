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

lemma mathd_algebra_141_1
  (a b : ℝ)
  (h₁ : a * b = (180 : ℝ))
  (sum_ab : a + b = (27 : ℝ))
  (square_identity : a ^ (2 : ℕ) + b ^ (2 : ℕ) = (729 : ℝ) - a * b * (2 : ℝ))
  (h₂ : True) :
  (729 : ℝ) - a * b * (2 : ℝ) = (369 : ℝ) := by
  have h_main : (729 : ℝ) - a * b * (2 : ℝ) = (369 : ℝ) := by
    norm_num [h₁, mul_assoc] at *
    <;>
    nlinarith
    <;>
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]
    <;>
    nlinarith
  
  apply h_main
