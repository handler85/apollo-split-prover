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
theorem mathd_algebra_114 (a : ℝ) (h₀ : a = 8) :
    (16 * (a ^ 2) ^ ((1 : ℝ) / 3)) ^ ((1 : ℝ) / 3) = 4 := by
    have h₁ : (a ^ 2 : ℝ) = 64 := by
        rw [h₀]
        norm_num
        <;> ring_nf
        <;> norm_num
    have h₂ : ((a ^ 2 : ℝ) ^ ((1 : ℝ) / 3)) = 4 := by
        rw [h₁]
        have h₃ : (64 : ℝ) ^ ((1 : ℝ) / 3) = 4 := by
            rw [show (64 : ℝ) = 4 ^ 3 by norm_num]
      
      
            <;>
            ring_nf
            <;>
            norm_num
            try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
            sorry
        rw [h₃]
        <;> norm_num
    have h₃ : (16 * (a ^ 2) ^ ((1 : ℝ) / 3)) = 64 := by
        rw [h₂]
        <;> norm_num
        <;>
        ring_nf at *
        <;>
        nlinarith [sq_nonneg (a - 8), sq_nonneg (a + 8)]
    have h₄ : (16 * (a ^ 2) ^ ((1 : ℝ) / 3)) ^ ((1 : ℝ) / 3) = 4 := by
        rw [h₃]
        have h₅ : (64 : ℝ) ^ ((1 : ℝ) / 3) = 4 := by
            rw [show (64 : ℝ) = 4 ^ 3 by norm_num]
      
      
            <;>
            ring_nf
            <;>
            norm_num
            simp_all only [one_div]
        rw [h₅]
        <;> norm_num
    rw [h₄]
    <;> norm_num