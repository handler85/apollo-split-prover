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
theorem amc12b_2020_p6 (n : ℕ) (h₀ : 9 ≤ n) : ∃ x : ℕ, (x : ℝ) ^ 2 = ((n + 2)! - (n + 1)!)/n! := by
  have fact1 : (n + 2)! = (n + 2) * (n + 1) * n!  := by
    linarith
  have fact2 : (n + 1)! = (n + 1) * n!  := by
    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


    
    have h_main : (↑(n + (1 : ℕ))! : ℝ) = ((↑n : ℝ) + (1 : ℝ)) * n! := by
        have h₁ : (n : ℕ) ≥ 9 := by
            linarith
        have h₂ : (↑(n + (2 : ℕ))! : ℝ) = ((↑n : ℝ) + (2 : ℝ)) * ((↑n : ℝ) + (1 : ℝ)) * n! := by
            gcongr
        have h₃ : (↑(n + (1 : ℕ))! : ℝ) = ((↑n : ℝ) + (1 : ℝ)) * n! := by
            have h₄ : (n : ℕ) ≥ 9 := by
                linarith
            have h₅ : (n : ℕ) ≥ 0 := by
                linarith
            have h₆ : (n + 2 : ℕ) ≥ 1 := by
                linarith
            have h₇ : (↑(n + (2 : ℕ))! : ℝ) = ((↑n : ℝ) + (2 : ℝ)) * ((↑n : ℝ) + (1 : ℝ)) * n! := by
                gcongr
            have h₈ : (↑(n + (1 : ℕ))! : ℝ) = ((↑n : ℝ) + (1 : ℝ)) * n! := by
                have h₉ : (n + 2 : ℕ) ≥ 1 := by
                    linarith
                have h₁₀ : (↑(n + (2 : ℕ))! : ℝ) = ((↑n : ℝ) + (2 : ℝ)) * ((↑n : ℝ) + (1 : ℝ)) * n! := by
                    gcongr
                have h₁₁ : (↑(n + (2 : ℕ))! : ℝ) = ((↑n : ℝ) + (2 : ℝ)) * ((↑n : ℝ) + (1 : ℝ)) * n! := by
                    gcongr
                have h₁₂ : (↑(n + (1 : ℕ))! : ℝ) = ((↑n : ℝ) + (1 : ℝ)) * n! := by
                    have h₁₃ : (↑(n + (2 : ℕ))! : ℝ) = (↑(n + (2 : ℕ)) * ↑(n + (1 : ℕ)) * ↑n!) := by
                        simp [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_zero] at *
                        <;> ring_nf at * <;> simp_all [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_zero]
                        <;> nlinarith
                    rw [h₁₃] at h₁₁
                    have h₁₄ : ((↑n : ℝ) + (2 : ℝ)) * ((↑n : ℝ) + (1 : ℝ)) * n! = (↑(n + (2 : ℕ)) * ↑(n + (1 : ℕ)) * ↑n!) := by
                        linarith
                    have h₁₅ : (↑(n + (1 : ℕ))! : ℝ) = ((↑n : ℝ) + (1 : ℝ)) * n! := by
                        field_simp [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_zero] at h₁₄ ⊢
                        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
                        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


                        sorry


                    exact h₁₅
                exact h₁₂
            exact h₈
        exact h₃
    exact h_main

  have factorization : (n + 2)! - (n + 1)! = (n + 1) ^ 2 * n!  := by
    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
  have simplification : ((n + 2)! - (n + 1)!)/n! = (n + 1) ^ 2  := by
    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


    
    have h_main : (n! : ℝ) > 0 := by
        have h₁ : (n! : ℝ) > 0 := by
            have h₃ : (Nat.factorial n : ℝ) > 0 := by
                exact_mod_cast Nat.factorial_pos n
            try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
            try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


            sorry


        exact h₁
    have h_final : (↑n : ℝ) * n! * n!⁻¹ * (2 : ℝ) + (↑n : ℝ) ^ (2 : ℕ) * n! * n!⁻¹ + n! * n!⁻¹ = (1 : ℝ) + (↑n : ℝ) * (2 : ℝ) + (↑n : ℝ) ^ (2 : ℕ) := by
        have h₁ : (n! : ℝ) * n!⁻¹ = 1 := by
            have h₂ : (n! : ℝ) ≠ 0 := by
                linarith
            field_simp [h₂]
        have h₂ : (↑n : ℝ) * n! * n!⁻¹ * (2 : ℝ) + (↑n : ℝ) ^ (2 : ℕ) * n! * n!⁻¹ + n! * n!⁻¹ = (↑n : ℝ) * n! * n!⁻¹ * (2 : ℝ) + (↑n : ℝ) ^ (2 : ℕ) * n! * n!⁻¹ + n! * n!⁻¹ := by
            rfl
        rw [h₂]
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


        
        have h_main_goal : (1 : ℝ) + (↑n : ℝ) * n! * n!⁻¹ * (2 : ℝ) + (↑n : ℝ) ^ (2 : ℕ) * n! * n!⁻¹ = (1 : ℝ) + (↑n : ℝ) * (2 : ℝ) + (↑n : ℝ) ^ (2 : ℕ) := by
          have h₂ : n! * n!⁻¹ = 1 := by
            linarith
          have h₃ : (↑n : ℝ) * n! * n!⁻¹ = (↑n : ℝ) * 1 := by
            have h₄ : n! * n!⁻¹ = 1 := by linarith
            have h₅ : (↑n : ℝ) * n! * n!⁻¹ = (↑n : ℝ) * (n! * n!⁻¹) := by ring
            rw [h₅]
            rw [h₄]
            <;> ring
          have h₄ : (↑n : ℝ) ^ (2 : ℕ) * n! * n!⁻¹ = (↑n : ℝ) ^ (2 : ℕ) * 1 := by
            have h₅ : n! * n!⁻¹ = 1 := by linarith
            have h₆ : (↑n : ℝ) ^ (2 : ℕ) * n! * n!⁻¹ = (↑n : ℝ) ^ (2 : ℕ) * (n! * n!⁻¹) := by ring
            rw [h₆]
            rw [h₅]
            <;> ring
          simp_all [mul_assoc]
          <;> ring_nf
          <;> nlinarith
        exact h_main_goal


    exact h_final

  use (n + 1)
  exact try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
  sorry
