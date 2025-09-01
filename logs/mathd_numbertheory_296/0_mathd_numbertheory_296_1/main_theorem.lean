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
lemma mathd_numbertheory_296_1
    (n : ℕ)
    (h₀ : (2 : ℕ) ≤ n)
    (x t : ℕ)
    (h₄ : t ^ (4 : ℕ) = n)
    (h₅ : x ^ (3 : ℕ) = n)
    (h : (64 : ℕ) < t)
    (h₇ : (65 : ℕ) ≤ t)
    (h₈ : (17850625 : ℕ) ≤ n)
    (h₁₁ : (64 : ℕ) < x)
    (h₁₂ : (65 : ℕ) ≤ x)
    (h₁₃ : (274625 : ℕ) ≤ n) :
    False := by
    have h_x_ge : (274625 : ℕ) ≤ n := by
        have h₆ : x ≥ 65 := by
            linarith
        have h₇ : x ^ 3 ≥ 65 ^ 3 := by
            exact Nat.pow_le_pow_of_le_left h₆ 3
        have h₈ : x ^ 3 = n := by
            linarith
        have h₉ : n ≥ 274625 := by
            norm_num at h₇ h₈ ⊢ <;> omega
        linarith
    have h_false : False := by
        have h₁₄ : n ≤ 274624 := by
            by_contra h₁₄
            have h₁₅ : n ≥ 274625 := by
                omega
            have h₁₆ : x ≥ 65 := by
                omega
            have h₁₇ : x ^ 3 ≥ 65 ^ 3 := by
                exact Nat.pow_le_pow_of_le_left h₁₆ 3
            have h₁₈ : x ^ 3 = n := by
                linarith
            have h₁₉ : n ≥ 274625 := by
                omega
            try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
            try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
            sorry
        omega
    exact h_false