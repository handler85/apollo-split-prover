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
theorem mathd_algebra_342 (a d : ℝ) (h₀ : (∑ k in Finset.range 5, (a + k * d)) = 70)
    (h₁ : (∑ k in Finset.range 10, (a + k * d)) = 210) : a = 42 / 5 := by
    have h₂ : a + 2 * d = 14 := by
        have h₂₁ : (∑ k in Finset.range 5, (a + k * d)) = 70  := by
      
            try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
        simp [Finset.sum_range_succ, Finset.sum_range_zero, Finset.sum_range_one] at h₂₁
        ring_nf at h₂₁ ⊢
        nlinarith
    have h₃ : 8 * a + 41 * d = 182 := by
        have h₃₁ : (∑ k in Finset.range 10, (a + k * d)) = 210  := by
      
            try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
        simp [Finset.sum_range_succ, Finset.sum_range_zero, Finset.sum_range_one] at h₃₁
        ring_nf at h₃₁ ⊢
        nlinarith
    have h₄ : d = 14 / 5 := by
        have h₄₁ : d = 14 / 5 := by
            linarith
        exact h₄₁
    have h₅ : a = 42 / 5 := by
        have h₅₁ : a = 42 / 5 := by
            have h₅₂ : a + 2 * d = 14  := by
        
                try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
            have h₅₃ : 8 * a + 41 * d = 182  := by
        
                gcongr
            have h₅₄ : d = 14 / 5  := by
        
                try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
            have h₅₅ : a = 42 / 5 := by
                nlinarith
            exact h₅₅
        exact h₅₁
    rw [h₅]
    <;> norm_num
    <;> linarithgcongrgcongrgcongrgcongr