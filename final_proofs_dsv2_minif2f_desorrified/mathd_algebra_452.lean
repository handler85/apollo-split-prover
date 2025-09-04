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
theorem mathd_algebra_452 (a : ℕ → ℝ) (h₀ : ∀ n, a (n + 2) - a (n + 1) = a (n + 1) - a n)
    (h₁ : a 1 = 2 / 3) (h₂ : a 9 = 4 / 5) : a 5 = 11 / 15 := by
    have h_common_diff : a 2 - a 1 = 1 / 60 := by
    
    
    
    
    
    
    
    
    
    
        norm_num at *
    
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


        
        have h_main : (-2 / 3 : ℝ) + a (2 : ℕ) = (1 / 60 : ℝ) := by
          try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
          try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


          


        gcongr

    have h_a5 : a 5 = 11 / 15 := by
    
    
    
    
    
    
    
    
    
    
        norm_num at *
    
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


        
        have h_a2 : a 2 = (41 / 60 : ℝ) := by
          have h₃ : (-2 / 3 : ℝ) + a (2 : ℕ) = (1 / 60 : ℝ) := h_common_diff
          have h₄ : a (2 : ℕ) = (1 / 60 : ℝ) + 2 / 3 := by linarith
          rw [h₄]
          norm_num
          <;> ring_nf
          <;> linarith
        
        have h_a0 : a 0 = (13 / 20 : ℝ) := by
          have h₅ := h₀ 0
          have h₆ := h₀ 1
          have h₇ := h₀ 2
          have h₈ := h₀ 3
          have h₉ := h₀ 4
          have h₁₀ := h₀ 5
          have h₁₁ := h₀ 6
          have h₁₂ := h₀ 7
          have h₁₃ := h₀ 8
          simp [h₁, h_a2] at h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ h₁₃
          ring_nf at *
          nlinarith
        
        have h_a3 : a 3 = (7 / 10 : ℝ) := by
          have h₅ := h₀ 0
          have h₆ := h₀ 1
          have h₇ := h₀ 2
          have h₈ := h₀ 3
          have h₉ := h₀ 4
          have h₁₀ := h₀ 5
          have h₁₁ := h₀ 6
          have h₁₂ := h₀ 7
          have h₁₃ := h₀ 8
          simp [h₁, h_a2, h_a0] at h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ h₁₃
          <;> ring_nf at * <;> nlinarith
        
        have h_a4 : a 4 = (43 / 60 : ℝ) := by
          have h₅ := h₀ 0
          have h₆ := h₀ 1
          have h₇ := h₀ 2
          have h₈ := h₀ 3
          have h₉ := h₀ 4
          have h₁₀ := h₀ 5
          have h₁₁ := h₀ 6
          have h₁₂ := h₀ 7
          have h₁₃ := h₀ 8
          simp [h₁, h_a2, h_a0, h_a3] at h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ h₁₃
          <;> ring_nf at * <;> nlinarith
        
        have h_a5 : a 5 = (11 / 15 : ℝ) := by
          have h₅ := h₀ 0
          have h₆ := h₀ 1
          have h₇ := h₀ 2
          have h₈ := h₀ 3
          have h₉ := h₀ 4
          have h₁₀ := h₀ 5
          have h₁₁ := h₀ 6
          have h₁₂ := h₀ 7
          have h₁₃ := h₀ 8
          simp [h₁, h_a2, h_a0, h_a3, h_a4] at h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ h₁₃
          <;> ring_nf at * <;> nlinarith
        
        exact h_a5


    exact h_a5