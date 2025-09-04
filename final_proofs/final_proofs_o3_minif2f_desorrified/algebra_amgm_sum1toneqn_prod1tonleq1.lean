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
theorem algebra_amgm_sum1toneqn_prod1tonleq1 (a : ℕ → NNReal) (n : ℕ)
    (h₀ : (∑ x in Finset.range n, a x) = n) : (∏ x in Finset.range n, a x) ≤ 1 := by
    have amgm_ineq : (∏ x in Finset.range n, a x)^(1 / n) ≤ ((∑ x in Finset.range n, a x) / n)  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


        
        have h_main : (∏ x ∈ Finset.range n, a x) ^ ((1 : ℕ) / n) ≤ (↑n : NNReal) / (↑n : NNReal) := by
        
            try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


            


        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
        <;> simp_all
        <;> linarith

    have substituted : (∏ x in Finset.range n, a x)^(1 / n) ≤ (n / n)  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
    have simplification : (n / n) = 1  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


        
        have h_main : n / n = (1 : ℕ) := by
          cases n with
          | zero =>
            simp_all [Finset.sum_range_zero]
          | succ n =>
            simp [Nat.div_self (Nat.succ_pos n)]
        exact h_main


    have geo_mean_bound : (∏ x in Finset.range n, a x)^(1 / n) ≤ 1 := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


        
        have h_main : (∏ x ∈ Finset.range n, a x) ^ ((1 : ℕ) / n) ≤ (1 : NNReal) := by
          have h₁ : (n : NNReal) / (n : NNReal) = 1 := by
            by_cases h : n = 0
            · simp [h]
              <;>
              aesop
            · field_simp [h]
              <;>
              aesop
          have h₂ : (∏ x ∈ Finset.range n, a x) ^ ((1 : ℕ) / n) ≤ (↑n : NNReal) / (↑n : NNReal) := substituted
          have h₃ : (↑n : NNReal) / (↑n : NNReal) = 1 := by
            by_cases h : n = 0
            · simp [h]
              <;>
              aesop
            · field_simp [h]
              <;>
              aesop
          calc
            (∏ x ∈ Finset.range n, a x) ^ ((1 : ℕ) / n) ≤ (↑n : NNReal) / (↑n : NNReal) := h₂
            _ = 1 := by simp [h₃]
            _ ≤ (1 : NNReal) := by simp
        exact h_main


    have power_monotonicity : ((∏ x in Finset.range n, a x)^(1 / n))^n ≤ (1)^n  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


        
        have h_main : (∏ x ∈ Finset.range n, a x) ^ ((1 : ℕ) / n * n) ≤ (1 : NNReal) := by
            have h₁ : (∏ x ∈ Finset.range n, a x) ^ ((1 : ℕ) / n * n) = ((∏ x ∈ Finset.range n, a x) ^ ((1 : ℕ) / n)) ^ n := by
                rw [← pow_mul]
                <;> simp [mul_comm]
                <;> ring_nf
            rw [h₁]
            have h₂ : ((∏ x ∈ Finset.range n, a x) ^ ((1 : ℕ) / n)) ^ n ≤ (1 : NNReal) ^ n := by
                have h₃ : (∏ x ∈ Finset.range n, a x) ^ ((1 : ℕ) / n) ≤ (1 : NNReal) := by
                    simpa [NNReal.coe_one] using geo_mean_bound
        
                gcongr
            have h₃ : (1 : NNReal) ^ n = (1 : NNReal)  := by
                simp
            rw [h₃] at h₂
            exact h₂
        exact h_main

    have one_power : 1^n = 1  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
    have product_eq : (∏ x in Finset.range n, a x) = ((∏ x in Finset.range n, a x)^(1 / n))^n  := by
        exact le_of_le_of_eq amgm_ineq (congrFun (congrArg HDiv.hDiv h₀) (↑n : NNReal))
    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarithgcongrexact Nat.one_pow n
    
