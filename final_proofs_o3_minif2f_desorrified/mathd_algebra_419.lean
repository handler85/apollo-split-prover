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
theorem mathd_algebra_419 (a b : ℝ) (h₀ : a = -1) (h₁ : b = 5) : -a - b ^ 2 + 3 * (a * b) = -39 := by
  have step1 : -a = -(-1)  := by
    linarith
  have step2 : -(-1) = 1  := by
    linarith
  have step3 : b^2 = 5^2  := by
    exact congrFun (congrArg HPow.hPow h₁) (2 : ℕ)
  have step4 : 5^2 = 25  := by
    linarith
  have step5 : 3 * (a * b) = 3 * ((-1) * 5)  := by
    simp_all only [neg_neg, neg_mul, one_mul, mul_neg]
  have step6 : (-1) * 5 = -5  := by
    linarith
  have step7 : 3 * (-5) = -15  := by
    linarith
  have step8 : -a - b^2 + 3 * (a * b) = 1 - 25 - 15  := by
    linarith
  have step9 : 1 - 25 - 15 = -39  := by
    linarith
  exact try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
  
