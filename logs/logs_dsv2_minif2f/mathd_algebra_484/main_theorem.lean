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
theorem mathd_algebra_484 : Real.log 27 / Real.log 3 = 3 := by
    have h_main : Real.log 27 = 3 * Real.log 3 := by
        have h₁ : Real.log 27 = Real.log (3 ^ 3)  := by
            norm_num
        rw [h₁]
        have h₂ : Real.log (3 ^ 3) = 3 * Real.log 3 := by
            rw [Real.log_pow] <;> norm_num
        rw [h₂]
        <;> ring
        <;> norm_num
    have h_final : Real.log 27 / Real.log 3 = 3 := by
        have h₁ : Real.log 3 ≠ 0 := by
            have h₂ : Real.log 3 > 0  := by
        
                try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
                sorry
            linarith
        rw [h_main]
        field_simp [h₁]
        <;> ring
        <;> norm_num
    rw [h_final]
    <;> norm_num