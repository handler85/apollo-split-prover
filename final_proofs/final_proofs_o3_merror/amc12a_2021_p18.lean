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
theorem amc12a_2021_p18 (f : ℚ → ℝ)
    (h₀ : ∀ x > 0, ∀ y > 0, f (x * y) = f x + f y)
    (h₁ : ∀ p, Nat.Prime p → f p = p) : f (25 / 11) < 0 := by
    have f_one : f 1 = 0 := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


        
        have h_main : f (1 : ℚ) = (0 : ℝ) := by
          have h₂ : f ((1 : ℚ) * (1 : ℚ)) = f (1 : ℚ) + f (1 : ℚ) := by
            have h₃ := h₀ (1 : ℚ) (by norm_num) (1 : ℚ) (by norm_num)
            simpa using h₃
          have h₄ : f ((1 : ℚ) * (1 : ℚ)) = f (1 : ℚ) := by
            norm_num
          have h₅ : f (1 : ℚ) + f (1 : ℚ) = f (1 : ℚ) := by linarith
          have h₆ : f (1 : ℚ) = 0 := by linarith
          exact h₆
        exact h_main


    have f_inv : ∀ (x : ℚ), x > 0 → f (1/x) = - f x := by
        intros x hx
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


        
        have h_main : f (x * x⁻¹) = f x + f x⁻¹ := by
          have h₂ := h₀ x hx (x⁻¹) (by
            -- Prove that x⁻¹ is positive since x is positive
            exact inv_pos.mpr hx)
          simpa [mul_comm] using h₂
        
        have h_product : x * x⁻¹ = (1 : ℚ) := by
          have h₂ : x ≠ 0 := by positivity
          field_simp [h₂]
          <;> ring_nf
          <;> simp_all
          <;> aesop
        
        have h_f_one : f (x * x⁻¹) = (0 : ℝ) := by
          rw [h_product]
          simp [f_one]
          <;> norm_cast
          <;> simp_all
        
        have h_final : f x⁻¹ = -f x := by
          have h₃ : f (x * x⁻¹) = f x + f x⁻¹ := h_main
          have h₄ : f (x * x⁻¹) = (0 : ℝ) := h_f_one
          have h₅ : f x + f x⁻¹ = 0 := by linarith
          have h₆ : f x⁻¹ = -f x := by linarith
          exact h₆
        
        exact h_final


    have f_pow : ∀ (p : ℕ) (n : ℕ), Nat.Prime p → f (p^n : ℚ) = n * p := by
        intros p n hp
        induction n with
            | zero =>
                simp_all only [gt_iff_lt, one_div, pow_zero, CharP.cast_eq_zero, zero_mul]
            | succ n ih =>
                try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


                
                have h_main : f ((↑p : ℚ) * (↑p : ℚ) ^ n) = f ((↑p : ℚ)) + f ((↑p : ℚ) ^ n) := by
                  have h₂ : (0 : ℚ) < (p : ℚ) := by
                    exact_mod_cast Nat.Prime.pos hp
                  have h₃ : (0 : ℚ) < ((p : ℚ) : ℚ) ^ n := by
                    exact pow_pos h₂ n
                  have h₄ : f ((↑p : ℚ) * (↑p : ℚ) ^ n) = f ((↑p : ℚ)) + f ((↑p : ℚ) ^ n) := by
                    have h₅ := h₀ (p : ℚ) h₂ ((↑p : ℚ) ^ n) h₃
                    simpa [mul_comm] using h₅
                  exact h₄
                
                have h_final : f ((↑p : ℚ) * (↑p : ℚ) ^ n) = (↑n : ℝ) * (↑p : ℝ) + (↑p : ℝ) := by
                  have h₂ : f ((↑p : ℚ)) = (↑p : ℝ) := by
                    have h₃ : f (↑p : ℚ) = (↑p : ℝ) := by
                      exact h₁ p hp
                    exact h₃
                  have h₃ : f ((↑p : ℚ) * (↑p : ℚ) ^ n) = f ((↑p : ℚ)) + f ((↑p : ℚ) ^ n) := h_main
                  rw [h₃]
                  have h₄ : f ((↑p : ℚ) ^ n) = (↑n : ℝ) * (↑p : ℝ) := by
                    simpa using ih
                  rw [h₂, h₄]
                  <;> ring
                  <;> field_simp
                  <;> linarith
                
                exact h_final


    have f_25 : f 25 = 10 := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


        
        have h_main : f (25 : ℚ) = (10 : ℝ) := by
          have h₂ : f ((5 : ℚ) ^ 2) = (2 : ℝ) * (5 : ℝ) := by
            have h₂₁ : f ((5 : ℚ) ^ 2) = (2 : ℝ) * (5 : ℝ) := by
              have h₂₂ : f ((5 : ℚ) ^ 2) = f ((↑(5 : ℕ) : ℚ) ^ (2 : ℕ)) := by norm_cast
              rw [h₂₂]
              have h₂₃ : f ((↑(5 : ℕ) : ℚ) ^ (2 : ℕ)) = ( (2 : ℝ) : ℝ) * ( (5 : ℝ) : ℝ) := by
                have h₂₄ := f_pow 5 2 (by decide)
                norm_num at h₂₄ ⊢
                <;> linarith
              simpa using h₂₃
            exact h₂₁
          norm_num [pow_two] at h₂ ⊢
          <;>
          (try simp_all [mul_comm]) <;>
          (try norm_num at * <;> linarith) <;>
          (try linarith [h₁ 5 (by decide)]) <;>
          (try
            {
              have h₃ := h₀ 5 (by norm_num) 5 (by norm_num)
              norm_num [mul_comm] at h₃
              <;> linarith
            }) <;>
          (try
            {
              have h₃ := h₀ 5 (by norm_num) (1/5) (by norm_num)
              norm_num [mul_comm] at h₃
              <;> linarith
            })
          <;>
          (try
            {
              have h₃ := h₀ 2 (by norm_num) 5 (by norm_num)
              norm_num [mul_comm] at h₃
              <;> linarith
            })
          <;>
          (try
            {
              have h₃ := h₀ 2 (by norm_num) (25) (by norm_num)
              norm_num [mul_comm] at h₃
              <;> linarith
            })
          <;>
          (try
            {
              have h₃ := h₀ 5 (by norm_num) (1/5) (by norm_num)
              norm_num [mul_comm] at h₃
              <;> linarith
            })
          <;>
          (try
            {
              have h₃ := h₀ 2 (by norm_num) (1/2) (by norm_num)
              norm_num [mul_comm] at h₃
              <;> linarith
            })
          <;>
          (try
            {
              have h₃ := h₀ 3 (by norm_num) 3 (by norm_num)
              norm_num [mul_comm] at h₃
              <;> linarith
            })
          <;>
          (try
            {
              have h₃ := h₀ 3 (by norm_num) (1/3) (by norm_num)
              norm_num [mul_comm] at h₃
              <;> linarith
            })
          <;>
          (try
            {
              have h₃ := h₀ 5 (by norm_num) 5 (by norm_num)
              norm_num [mul_comm] at h₃
              <;> linarith
            })
          <;>
          (try
            {
              have h₃ := h₀ 2 (by norm_num) 5 (by norm_num)
              norm_num [mul_comm] at h₃
              <;> linarith
            })
          <;>
          (try
            {
              have h₃ := h₀ 5 (by norm_num) 2 (by norm_num)
              norm_num [mul_comm] at h₃
              <;> linarith
            })
          <;>
          (try
            {
              have h₃ := h₀ 3 (by norm_num) 5 (by norm_num)
              norm_num [mul_comm] at h₃
              <;> linarith
            })
          <;>
          (try
            {
              have h₃ := h₀ 5 (by norm_num) 3 (by norm_num)
              norm_num [mul_comm] at h₃
              <;> linarith
            })
        exact h_main


    have f_11 : f 11 = 11 := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


        
        have h_main : f (11 : ℚ) = (11 : ℝ) := by
          have h₂ := f_pow 11 1 (by norm_num [Nat.Prime])
          norm_num at h₂ ⊢
          <;>
          (try norm_num) <;>
          (try linarith) <;>
          (try simp_all [mul_comm]) <;>
          (try ring_nf at * <;> nlinarith)
          <;>
          (try nlinarith) <;>
          (try linarith) <;>
          (try
            {
              have h₃ := f_pow 5 2 (by norm_num [Nat.Prime])
              have h₄ := f_pow 5 1 (by norm_num [Nat.Prime])
              norm_num at h₃ h₄ ⊢
              <;> nlinarith [h₀ 5 (by norm_num) 11 (by norm_num)]
            })
          <;>
          (try
            {
              have h₃ := f_pow 2 5 (by norm_num [Nat.Prime])
              have h₄ := f_pow 2 4 (by norm_num [Nat.Prime])
              have h₅ := f_pow 2 3 (by norm_num [Nat.Prime])
              have h₆ := f_pow 2 2 (by norm_num [Nat.Prime])
              have h₇ := f_pow 2 1 (by norm_num [Nat.Prime])
              norm_num at h₃ h₄ h₅ h₆ h₇ ⊢
              <;> nlinarith [h₀ 2 (by norm_num) 11 (by norm_num)]
            })
          <;>
          (try
            {
              have h₃ := f_pow 3 2 (by norm_num [Nat.Prime])
              have h₄ := f_pow 3 1 (by norm_num [Nat.Prime])
              norm_num at h₃ h₄ ⊢
              <;> nlinarith [h₀ 3 (by norm_num) 11 (by norm_num)]
            })
          <;>
          (try
            {
              have h₃ := f_pow 5 2 (by norm_num [Nat.Prime])
              have h₄ := f_pow 5 1 (by norm_num [Nat.Prime])
              norm_num at h₃ h₄ ⊢
              <;> nlinarith [h₀ 5 (by norm_num) 11 (by norm_num)]
            })
          <;>
          (try
            {
              have h₃ := f_pow 7 1 (by norm_num [Nat.Prime])
              have h₄ := f_pow 7 2 (by norm_num [Nat.Prime])
              norm_num at h₃ h₄ ⊢
              <;> nlinarith [h₀ 7 (by norm_num) 11 (by norm_num)]
            })
          <;>
          (try
            {
              have h₃ := f_pow 11 1 (by norm_num [Nat.Prime])
              norm_num at h₃ ⊢
              <;> nlinarith
            })
        exact h_main


    have f_div : f (25 / 11) = f 25 + f (1/11) := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


        
        have h_f_inv_11 : f (11 : ℚ) = (11 : ℝ) := by
          simpa [h₁] using f_11
        
        have h_f_inv_5 : f (5 : ℚ) = (5 : ℝ) := by
          have h2 : f (5 : ℚ) = (5 : ℝ) := by
            have h3 := h₀ 5 (by norm_num) 5 (by norm_num)
            have h4 := h₀ 5 (by norm_num) (1 / 5 : ℚ) (by norm_num)
            have h5 := h₀ (11 : ℚ) (by norm_num) (1 / 11 : ℚ) (by norm_num)
            have h6 := h₀ (25 : ℚ) (by norm_num) (1 / 25 : ℚ) (by norm_num)
            norm_num [f_one, f_inv, f_pow, h₁, Nat.cast_one] at *
            <;>
            (try ring_nf at * <;> nlinarith) <;>
            (try linarith [h₁ 5 (by decide), h₁ 11 (by decide), h₁ 25 (by decide)]) <;>
            (try field_simp [h₁] at *) <;>
            (try norm_cast at *) <;>
            (try linarith)
          exact h2
        
        have h_f_inv_inv_11 : f ((11 : ℚ)⁻¹) = (-(11 : ℝ)) := by
          have h₂ : f ((11 : ℚ)⁻¹) = -f (11 : ℚ) := by
            apply f_inv 11
            norm_num
          rw [h₂]
          <;> simp [h_f_inv_11]
          <;> norm_num
          <;> linarith
        
        have h_f_inv_25 : f ((25 : ℚ) / 11) = (-1 : ℝ) := by
          have h₃ : f ((25 : ℚ) / 11) = f (25 : ℚ) + f ((11 : ℚ)⁻¹) := by
            have h₄ := h₀ (25 : ℚ) (by norm_num) ((11 : ℚ)⁻¹) (by norm_num)
            norm_num at h₄ ⊢
            <;>
            ring_nf at h₄ ⊢ <;>
            nlinarith
          rw [h₃]
          have h₄ : f (25 : ℚ) = (10 : ℝ) := f_25
          have h₅ : f ((11 : ℚ)⁻¹) = (-(11 : ℝ)) := h_f_inv_inv_11
          rw [h₄, h₅]
          <;> norm_num
          <;> linarith
        
        exact h_f_inv_25


    have f_div_simpl : f (25 / 11) = 10 - 11 := by
        rw [f_div, f_25, f_inv 11 (by norm_num), f_11]
        linarith
    rw [f_div_simpl]
    linarith