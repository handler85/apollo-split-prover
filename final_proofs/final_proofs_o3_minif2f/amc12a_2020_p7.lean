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
theorem amc12a_2020_p7 (a : ℕ → ℕ)
    (h₀ : a 0 ^ 3 = 1) (h₁ : a 1 ^ 3 = 8) (h₂ : a 2 ^ 3 = 27)
    (h₃ : a 3 ^ 3 = 64) (h₄ : a 4 ^ 3 = 125) (h₅ : a 5 ^ 3 = 216) (h₆ : a 6 ^ 3 = 343) :
    ∑ k in Finset.range 7, 6 * ((a k) ^ 2 : ℤ) - 2 * ∑ k in Finset.range 6, (a k) ^ 2 = 658 := by 
    have ha0 : a 0 = 1  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
    have ha1 : a 1 = 2  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


        
        have h_main : a 1 = 2 := by
          have h₁' : a 1 ^ 3 = 8 := by simpa using h₁
          have h₂' : a 1 = 2 := by
            -- We know that 2^3 = 8, so a 1 must be 2
            have h₇ : a 1 ≤ 2 := by
              -- Prove that a 1 ≤ 2 by contradiction
              by_contra! h
              -- If a 1 > 2, then a 1 ≥ 3, which implies a 1 ^ 3 ≥ 27, contradicting a 1 ^ 3 = 8
              have h₈ : a 1 ≥ 3 := by omega
              have h₉ : a 1 ^ 3 ≥ 3 ^ 3 := by
                exact Nat.pow_le_pow_of_le_left (by omega) 3
              have h₁₀ : 3 ^ 3 = 27 := by norm_num
              have h₁₁ : a 1 ^ 3 ≥ 27 := by omega
              omega
            have h₈ : a 1 ≥ 1 := by
              by_contra! h
              have h₉ : a 1 = 0 := by omega
              rw [h₉] at h₁'
              norm_num at h₁'
              <;> simp_all
              <;> norm_num
              <;> nlinarith
            interval_cases a 1 <;> norm_num at h₁' ⊢ <;>
              (try omega) <;> (try contradiction) <;> (try aesop)
          exact h₂'
        exact h_main


    have ha2 : a 2 = 3  := by
        exact eq_one_of_mul_eq_one_left h₀
    have ha3 : a 3 = 4  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


        
        have h_main : a (3 : ℕ) = (4 : ℕ) := by
          have h7 : a (3 : ℕ) ^ 3 = 64 := h₃
          have h8 : a (3 : ℕ) ≤ 6 := by
            by_contra h
            have h9 : a (3 : ℕ) ≥ 7 := by
              omega
            have h10 : a (3 : ℕ) ^ 3 ≥ 7 ^ 3 := by
              exact Nat.pow_le_pow_of_le_left (by omega) 3
            have h11 : 7 ^ 3 = 343 := by norm_num
            have h12 : a (3 : ℕ) ^ 3 ≥ 343 := by
              omega
            omega
          interval_cases a (3 : ℕ) <;> norm_num at h7 ⊢ <;>
          (try omega) <;> (try
            {
              simp_all [pow_three]
              <;> ring_nf at *
              <;> omega
            }) <;> (try
            {
              omega
            })
          <;> omega
        
        exact h_main


    have ha4 : a 4 = 5  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


        
        have h_main : a (4 : ℕ) = (5 : ℕ) := by
          have h₇ : a (4 : ℕ) ^ (3 : ℕ) = (125 : ℕ) := h₄
          have h₈ : a (4 : ℕ) ≤ 5 := by
            by_contra! h
            have h₉ : a (4 : ℕ) ≥ 6 := by omega
            have h₁₀ : a (4 : ℕ) ^ (3 : ℕ) ≥ 6 ^ (3 : ℕ) := by
              exact Nat.pow_le_pow_of_le_left (by omega) 3
            have h₁₁ : 6 ^ (3 : ℕ) = 216 := by norm_num
            have h₁₂ : a (4 : ℕ) ^ (3 : ℕ) ≥ 216 := by
              omega
            omega
          have h₉ : a (4 : ℕ) ≥ 5 := by
            by_contra! h
            have h₁₀ : a (4 : ℕ) ≤ 4 := by omega
            have h₁₁ : a (4 : ℕ) ^ (3 : ℕ) ≤ 4 ^ (3 : ℕ) := by
              exact Nat.pow_le_pow_of_le_left h₁₀ 3
            have h₁₂ : 4 ^ (3 : ℕ) = 64 := by norm_num
            have h₁₃ : a (4 : ℕ) ^ (3 : ℕ) ≤ 64 := by
              omega
            omega
          have h₁₀ : a (4 : ℕ) = 5 := by
            interval_cases a (4 : ℕ) <;> norm_num at h₇ ⊢ <;>
              (try omega) <;>
              (try { contradiction }) <;>
              (try { linarith })
          exact h₁₀
        exact h_main


    have ha5 : a 5 = 6  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


        
        have h₇ : a (5 : ℕ) ≤ 6 := by
          by_contra h
          have h₇ : a (5 : ℕ) ≥ 7 := by omega
          have h₈ : a (5 : ℕ) ^ (3 : ℕ) ≥ 7 ^ (3 : ℕ) := by
            have h₉ : a (5 : ℕ) ≥ 7 := by omega
            have h₁₀ : a (5 : ℕ) ^ (3 : ℕ) ≥ 7 ^ (3 : ℕ) := by
              exact Nat.pow_le_pow_of_le_left h₉ 3
            exact h₁₀
          have h₉ : 7 ^ (3 : ℕ) > 216 := by norm_num
          have h₁₀ : a (5 : ℕ) ^ (3 : ℕ) > 216 := by omega
          omega
        
        have h₈ : a (5 : ℕ) ≥ 6 := by
          by_contra h
          have h₉ : a (5 : ℕ) ≤ 5 := by omega
          have h₁₀ : a (5 : ℕ) ^ (3 : ℕ) ≤ 5 ^ (3 : ℕ) := by
            exact Nat.pow_le_pow_of_le_left h₉ 3
          have h₁₁ : 5 ^ (3 : ℕ) = 125 := by norm_num
          have h₁₂ : a (5 : ℕ) ^ (3 : ℕ) ≤ 125 := by
            omega
          have h₁₃ : a (5 : ℕ) ^ (3 : ℕ) = 216 := h₅
          omega
        
        have h₉ : a (5 : ℕ) = 6 := by
          have h₁₀ : a (5 : ℕ) ≤ 6 := h₇
          have h₁₁ : a (5 : ℕ) ≥ 6 := h₈
          have h₁₂ : a (5 : ℕ) = 6 := by
            omega
          exact h₁₂
        
        simpa using h₉


    have ha6 : a 6 = 7  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


        
        have h_main : a (6 : ℕ) = 7 := by
          have h₇ : a (6) ^ 3 = 343 := h₆
          have h₈ : a (6) ≤ 9 := by
            by_contra! h
            have h₉ : a (6) ≥ 10 := by linarith
            have h₁₀ : a (6) ^ 3 ≥ 10 ^ 3 := by
              exact Nat.pow_le_pow_of_le_left (by linarith) 3
            nlinarith
          interval_cases a (6) <;> norm_num at h₇ ⊢ <;>
          (try contradiction) <;>
          (try omega) <;>
          (try
            {
              simp_all [pow_succ]
              <;> ring_nf at *
              <;> omega
            })
          <;>
          (try
            {
              nlinarith
            })
          <;>
          (try
            {
              omega
            })
        exact h_main


    have total_area_separate : ∑ k in Finset.range 7, 6 * ((a k) ^ 2 : ℤ) = 6 * (1^2 + 2^2 + 3^2 + 4^2 + 5^2 + 6^2 + 7^2)  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


        
        have h_main : ∑ x ∈ Finset.range (7 : ℕ), a x ^ (2 : ℕ) * (6 : ℕ) = 840 := by
          simp [Finset.sum_range_succ, ha0, ha1, ha2, ha3, ha4, ha5, ha6, pow_two]
          <;> norm_num
          <;> rfl
        exact h_main


    have total_overlap : 2 * ∑ k in Finset.range 6, (a k) ^ 2 = 2 * (1^2 + 2^2 + 3^2 + 4^2 + 5^2 + 6^2)  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


        
        have h_sum_7 : (∑ x ∈ Finset.range (7 : ℕ), (a x : ℕ)^2) = 140 := by
          simp [Finset.sum_range_succ, ha0, ha1, ha2, ha3, ha4, ha5, ha6, pow_two]
          <;> norm_num
          <;> rfl
        
        have h_sum_6 : (∑ x ∈ Finset.range (6 : ℕ), a x ^ (2 : ℕ)) = 91 := by
          simp [Finset.sum_range_succ, ha0, ha1, ha2, ha3, ha4, ha5, ha6, pow_two] at *
          <;> norm_num
          <;> rfl
        
        have h_main : (∑ x ∈ Finset.range (6 : ℕ), a x ^ (2 : ℕ)) * (2 : ℕ) = (182 : ℕ) := by
          rw [h_sum_6]
          <;> norm_num
          <;> rfl
        
        exact h_main


    have sum7 : 1^2 + 2^2 + 3^2 + 4^2 + 5^2 + 6^2 + 7^2 = 140  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
    have sum6 : 1^2 + 2^2 + 3^2 + 4^2 + 5^2 + 6^2 = 91  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
    have total_exposed : 6 * 140 - 2 * 91 = 658  := by
        linarith
    linarithlinarithomega