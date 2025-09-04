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
theorem mathd_algebra_275 (x : ℝ) (h : ((11 : ℝ)^(1/4))^(3*x - 3) = 1/5) :
    ((11 : ℝ)^(1/4))^(6*x + 2) = 121 / 25 := by
  let a := (11 : ℝ)^(1/4)
  have step1 : 6 * x + 2 = 2 * (3 * x - 3) + 8  := by
    linarith
  have step2 : a^(6 * x + 2) = a^(2 * (3 * x - 3)) * a^8  := by
    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
  have step3 : a^(2 * (3 * x - 3)) = (a^(3 * x - 3))^2  := by
    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
  have step4 : (a^(3 * x - 3))^2 = (1 / 5)^2  := by
    exact congrFun (congrArg HPow.hPow h) (2 : ℕ)
  have step5 : (1 / 5)^2 = 1 / 25  := by
    omega
  have step6 : a^4 = 11  := by
    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
  have step7 : a^8 = (a^4)^2  := by
    linarith
  have step8 : (a^4)^2 = 11^2  := by
    exact congrFun (congrArg HPow.hPow step6) (2 : ℕ)
  have step9 : 11^2 = 121  := by
    linarith
  have step10 : a^(6 * x + 2) = (1 / 25) * 121  := by
    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
  exact try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
  
