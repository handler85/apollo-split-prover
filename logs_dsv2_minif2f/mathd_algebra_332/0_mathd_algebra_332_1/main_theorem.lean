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

lemma mathd_algebra_332_1
  (x y : ℝ)
  (h_sum : x + y = (14 : ℝ))
  (h₄ : √(x * y) = √(19 : ℝ))
  (h : x * y < (0 : ℝ))
  (h₀ : True) :
  False := by
  have h₁ : False := by
    have h₂ : x * y < 0 := h
    have h₃ : √(x * y) = 0 := by
      rw [Real.sqrt_eq_zero_of_nonpos] <;> linarith
    have h₄' : √(19 : ℝ) > 0 := by positivity
    have h₅ : √(x * y) = √(19 : ℝ) := h₄
    rw [h₃] at h₅
    norm_num at h₅
    <;>
    (try contradiction) <;>
    nlinarith [Real.sqrt_nonneg 19, Real.sq_sqrt (show (0 : ℝ) ≤ 19 by norm_num)]
  exact h₁
