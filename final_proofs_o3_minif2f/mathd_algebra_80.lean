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
theorem mathd_algebra_80 (x : ℝ) (h₀ : x ≠ -1) (h₁ : (x - 9) / (x + 1) = 2) : x = -11 := by
  have step1 : x - 9 = 2 * (x + 1) := by
    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


    
    have h₂ : x = -11 := by
        have h₃ : (1 + x) ≠ 0 := by
            intro h
            apply h₀
            linarith
        field_simp [h₃] at h₁
        ring_nf at h₁
        apply mul_left_cancel₀ (sub_ne_zero.mpr h₃)
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


        
        have h_x : x = -11 := by
          have h₂ : x = -11 := by
            -- Solve for x using the equation -9 + x = 2 + 2 * x
            apply Eq.symm
            linarith
          exact h₂
        
        have h_main : x + x ^ (2 : ℕ) = (-11 : ℝ) - x * (11 : ℝ) := by
          rw [h_x]
          norm_num
          <;>
          ring_nf
          <;>
          norm_num
          <;>
          linarith
        
        rw [h_main]
        <;>
        norm_num
        <;>
        linarith


    have h₃ : (-9 : ℝ) + x = (2 : ℝ) + x * (2 : ℝ) := by
        rw [h₂]
        norm_num
        <;>
        linarith
    exact h₃

  have step2 : x - 9 = 2*x + 2 := by
    linarith
  have step3 : -9 = x + 2 := by
    linarith
  have step4 : x = -11 := by
    linarith
  exact step4