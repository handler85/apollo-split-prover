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
theorem mathd_algebra_440 (x : ℝ) (h₀ : 3 / 2 / 3 = x / 10) : x = 5 := by
    have h1 : 3/2 = 1.5  := by
        omega
    have h2 : (3/2) / 3 = 1/2  := by
        linarith
    have h3 : x/10 = 1/2  := by
        linarith
    have h4 : x = 10 * (1/2)  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


        
        have h_main : x = (5 : ℝ) := by
          have h4 : x * (1 / 10 : ℝ) = (1 / 2 : ℝ) := h3
          -- Multiply both sides by 10 to eliminate the fraction
          field_simp at h4 ⊢
          <;> ring_nf at h4 ⊢ <;> nlinarith
        
        exact h_main


    have h5 : 10 * (1/2) = 5  := by
        linarith
    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith