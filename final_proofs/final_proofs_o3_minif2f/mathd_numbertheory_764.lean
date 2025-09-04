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
theorem mathd_numbertheory_764 (p : ℕ) (h₀ : Nat.Prime p) (h₁ : 7 ≤ p) :
    (∑ k in Finset.Icc 1 (p - 2), (k : ZMod p)⁻¹ * ((k : ZMod p) + 1)⁻¹) = 2 := by
    have h_partial_fraction : ∀ k ∈ Finset.Icc 1 (p - 2), ((k : ZMod p) * ((k : ZMod p) + 1))⁻¹ = (k : ZMod p)⁻¹ - ((k : ZMod p) + 1)⁻¹ := by
        intros k hk
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


        
        have h_k_lt_p : k < p := by
            have h₂ : k ≤ p - 2 := by
                linarith
            have h₃ : 1 ≤ k := by
                linarith
            have h₄ : p - 2 + 1 ≤ p := by
                omega
            have h₅ : k < p := by
                by_contra h
                have h₆ : k ≥ p := by
                    omega
                have h₇ : p - 2 < p := by
                    omega
                have h₈ : k ≤ p - 2 := by
                    gcongr
                omega
            exact h₅
        have h_main : ((↑k : ZMod p) + (↑k : ZMod p) ^ (2 : ℕ))⁻¹ = (↑k : ZMod p)⁻¹ - ((1 : ZMod p) + (↑k : ZMod p))⁻¹ := by
            have h₂ : (k : ZMod p) ≠ 0 := by
                intro h
                have h₃ : (p : ℕ) ∣ k := by
                    simpa [h] using ZMod.natCast_zmod_eq_zero_iff_dvd k p
                have h₄ : (p : ℕ) ∣ k := by
                    assumption
                have h₅ : k < p := by
                    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
                have h₆ : p ∣ k := by
                    exact_mod_cast h₄
                have h₇ : p ≤ k := by
                    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
                    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


                    
                    have h_contradiction : False := by
                      have h₇ : p ∣ k := h₆
                      have h₈ : k ≥ p := by
                        have h₉ : p ∣ k := h₇
                        have h₁₀ : p ≤ k := Nat.le_of_dvd (by omega) h₉
                        omega
                      have h₉ : k < p := by
                        have h₁₀ : k ≤ p - 2 := hk.2
                        have h₁₁ : p ≥ 7 := by omega
                        have h₁₂ : p - 2 < p := by
                          have h₁₃ : p ≥ 7 := by omega
                          have h₁₄ : p - 2 < p := by
                            omega
                          exact h₁₄
                        omega
                      omega
                    
                    have h_main : p ≤ k := by
                      exfalso
                      exact h_contradiction
                    
                    exact h_main


                omega
            have h₃ : ((↑k : ZMod p) + (↑k : ZMod p) ^ 2)⁻¹ = ((↑k : ZMod p) * ((1 : ZMod p) + (↑k : ZMod p)))⁻¹ := by
                have h₄ : ((↑k : ZMod p) + (↑k : ZMod p) ^ 2) = (↑k : ZMod p) * ((1 : ZMod p) + (↑k : ZMod p)) := by
                    ring_nf
                    <;> simp [pow_two, Nat.cast_add, Nat.cast_one, Nat.cast_mul]
                    <;> ring_nf
                    <;> norm_num
                    <;> aesop
                rw [h₄]
                <;> simp [mul_add, add_mul, mul_comm, mul_left_comm]
                <;> ring_nf
            rw [h₃]
            <;> ring_nf
            <;> simp_all [mul_comm, mul_left_comm, mul_assoc]
            try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
            try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


            sorry


        rw [h_main]
        <;> norm_num
        <;> aesop

    have h_inv1 : (1 : ZMod p)⁻¹ = 1 := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
    exact ZMod.inv_one p