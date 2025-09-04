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
theorem mathd_algebra_478 (b h v : ℝ) 
    (h₀ : 0 < b ∧ 0 < h ∧ 0 < v) 
    (h₁ : v = 1 / 3 * (b * h))
    (h₂ : b = 30) (h₃ : h = 13 / 2) : v = 65 := by
    have step1 : b * h = 30 * (13 / 2) := by
        rw [h₂, h₃]
    have step2 : 30 * (13 / 2) = 195 := by
        linarith
    have step3 : b * h = 195 := by
        omega
    have step4 : v = 1 / 3 * 195 := by
        rw [h₁, step3]
    have step5 : 1 / 3 * 195 = 65 := by
        linarith
    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith