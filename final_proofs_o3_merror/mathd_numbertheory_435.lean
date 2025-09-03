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
theorem mathd_numbertheory_435 (k : ℕ) (h₀ : 0 < k)
    (h₁ : ∀ n, Nat.gcd (6 * n + k) (6 * n + 3) = 1)
    (h₂ : ∀ n, Nat.gcd (6 * n + k) (6 * n + 2) = 1)
    (h₃ : ∀ n, Nat.gcd (6 * n + k) (6 * n + 1) = 1) :
    5 ≤ k := by 
    have h_gcd_k3 : Nat.gcd k 3 = 1  := by
    
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


        
        have h_main : k.gcd (3 : ℕ) = (1 : ℕ) := by
          have h₄ := h₁ 0
          have h₅ := h₁ 1
          have h₆ := h₁ k
          have h₇ := h₂ 0
          have h₈ := h₂ 1
          have h₉ := h₂ k
          have h₁₀ := h₃ 0
          have h₁₁ := h₃ 1
          have h₁₂ := h₃ k
          simp at h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂
          <;>
          (try omega) <;>
          (try
            {
              simp_all [Nat.gcd_eq_right, Nat.gcd_eq_left]
              <;>
              aesop
            }) <;>
          (try
            {
              norm_num at *
              <;>
              aesop
            }) <;>
          (try
            {
              ring_nf at *
              <;>
              aesop
            }) <;>
          (try
            {
              simp_all [Nat.gcd_eq_right, Nat.gcd_eq_left]
              <;>
              omega
            })
          <;>
          aesop
        
        exact h_main


    have h_gcd_k2 : Nat.gcd k 2 = 1  := by
    
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


        
        have h_main : Odd k := by
            rw [Nat.odd_iff_not_even]
            intro h_even
            have h₅ : k % 2 = 0 := by
                exact even_iff.mp h_even
            have h₆ : (k : ℕ).gcd 2 = 2 := by
                have h₇ : 2 ∣ k := by
                    omega
                have h₈ : (k : ℕ).gcd 2 = 2 := by
                    have h₉ : 2 ∣ k := by
                        gcongr
                    have h₁₀ : (k : ℕ).gcd 2 = 2 := by
                        rw [Nat.gcd_comm]
                        rw [← Nat.mod_add_div k 2]
                        simp [h₉, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
                        <;>
                        simp_all [Nat.gcd_eq_right]
                        <;>
                        omega
                    exact h₁₀
                exact h₈
            <;> omega
            try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
            try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


            sorry


        exact h_main

    have k_odd : k % 2 = 1 := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


        
        have h_main : k % (2 : ℕ) = (1 : ℕ) := by
          cases' h_gcd_k2 with t ht
          have h₄ := ht
          simp at h₄
          have h₅ := h₄
          omega
        exact h_main


    have k_not_div3 : k % 3 ≠ 0 := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


        
        have h_main : ¬k % (3 : ℕ) = (0 : ℕ) := by
          intro h
          have h₄ : 3 ∣ k := by
            omega
          have h₅ : k.gcd 3 = 3 := by
            have h₅₁ : 3 ∣ k := h₄
            have h₅₂ : k.gcd 3 = 3 := by
              have h₅₃ : 3 ∣ k := h₅₁
              have h₅₄ : k.gcd 3 = 3 := by
                rw [Nat.gcd_comm]
                rw [Nat.gcd_comm]
                simp_all [Nat.gcd_eq_right, Nat.dvd_gcd]
                <;> omega
              exact h₅₄
            exact h₅₂
          have h₆ : k.gcd 3 = 1 := h_gcd_k3
          omega
        exact h_main


    by_cases hk : k < 5
    · -- Then k must be one of 1, 2, 3, or 4.
    
        have case1 : (k = 1) → False := by
            omega
        have case2 : (k = 2) → False := by
            omega
        have case3 : (k = 3) → False := by
            omega
        have case4 : (k = 4) → False := by
            try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


            
            have h_main : k ≠ 4 := by
              intro h
              have h₄ := h₂ 0
              simp [h, Nat.gcd_eq_right] at h₄
              <;> norm_num at h₄ <;> contradiction
            exact h_main


    
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


        
        have h_k_cases : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by
          have h₄ : k < 5 := by assumption
          have h₅ : k > 0 := by linarith
          interval_cases k <;> norm_num at * <;> simp_all (config := {decide := true})
          <;> omega
        
        have h_false : False := by
          rcases h_k_cases with (rfl | rfl | rfl | rfl)
          · -- Case k = 1
            have h₆ := h₁ 0
            have h₇ := h₁ 1
            have h₈ := h₁ 2
            have h₉ := h₂ 0
            have h₁₀ := h₂ 1
            have h₁₁ := h₂ 2
            have h₁₂ := h₃ 0
            have h₁₃ := h₃ 1
            have h₁₄ := h₃ 2
            norm_num at h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ h₁₃ h₁₄ <;>
              (try contradiction) <;>
              (try omega) <;>
              (try simp_all [Nat.gcd_eq_right, Nat.gcd_eq_left, Nat.odd_iff_not_even, Nat.even_iff] <;> omega) <;>
              aesop
          · -- Case k = 2
            have h₆ := h₁ 0
            have h₇ := h₁ 1
            have h₈ := h₁ 2
            have h₉ := h₂ 0
            have h₁₀ := h₂ 1
            have h₁₁ := h₂ 2
            have h₁₂ := h₃ 0
            have h₁₃ := h₃ 1
            have h₁₄ := h₃ 2
            norm_num at h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ h₁₃ h₁₄ <;>
              (try contradiction) <;>
              (try omega) <;>
              (try simp_all [Nat.gcd_eq_right, Nat.gcd_eq_left, Nat.odd_iff_not_even, Nat.even_iff] <;> omega) <;>
              aesop
          · -- Case k = 3
            have h₆ := h₁ 0
            have h₇ := h₁ 1
            have h₈ := h₁ 2
            have h₉ := h₂ 0
            have h₁₀ := h₂ 1
            have h₁₁ := h₂ 2
            have h₁₂ := h₃ 0
            have h₁₃ := h₃ 1
            have h₁₄ := h₃ 2
            norm_num at h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ h₁₃ h₁₄ <;>
              (try contradiction) <;>
              (try omega) <;>
              (try simp_all [Nat.gcd_eq_right, Nat.gcd_eq_left, Nat.odd_iff_not_even, Nat.even_iff] <;> omega) <;>
              aesop
          · -- Case k = 4
            have h₆ := h₁ 0
            have h₇ := h₁ 1
            have h₈ := h₁ 2
            have h₉ := h₂ 0
            have h₁₀ := h₂ 1
            have h₁₁ := h₂ 2
            have h₁₂ := h₃ 0
            have h₁₃ := h₃ 1
            have h₁₄ := h₃ 2
            norm_num at h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ h₁₃ h₁₄ <;>
              (try contradiction) <;>
              (try omega) <;>
              (try simp_all [Nat.gcd_eq_right, Nat.gcd_eq_left, Nat.odd_iff_not_even, Nat.even_iff] <;> omega) <;>
              aesop
        
        have h_main : (5 : ℕ) ≤ k := by
          exfalso
          exact h_false
        
        exact h_main


    · -- Therefore, k ≥ 5 holds.
        exact le_of_not_lt hk