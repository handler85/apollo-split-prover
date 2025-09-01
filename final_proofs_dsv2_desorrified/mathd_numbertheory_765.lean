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
theorem mathd_numbertheory_765 (x : ℤ) (h₀ : x < 0) (h₁ : 24 * x % 1199 = 15) : x ≤ -449 := by
    have h_main : x ≤ -449 := by
        by_contra! h
        have h₂ : x ≥ -448  := by
            linarith
        have h₃ : x ≥ -448  := by
            linarith
        have h₄ : 24 * x % 1199 = 15  := by
      
            gcongr
        have h₅ : x ≥ -448  := by
            linarith
        have h₆ : x ≤ 0  := by
            linarith
        have h₇ : x ≥ -448  := by
            linarith
        have h₈ : x ≤ 0  := by
            linarith
        interval_cases x <;> norm_num [Int.mul_emod, Int.emod_emod] at h₄ <;> omega
    exact h_main