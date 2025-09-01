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
theorem mathd_numbertheory_296 (n : ℕ) (h₀ : 2 ≤ n) (h₁ : ∃ x, x ^ 3 = n) (h₂ : ∃ t, t ^ 4 = n) :
    4096 ≤ n := by
    have h_main : 4096 ≤ n := by
        rcases h₁ with ⟨x, hx⟩
        rcases h₂ with ⟨t, ht⟩
        have h₃ : x ^ 3 = n  := by
            rw [hx]
        have h₄ : t ^ 4 = n  := by
            rw [ht]
        have h₅ : x ^ 3 = t ^ 4  := by
            linarith
        have h₆ : t ≤ 64 := by
            by_contra! h
            have h₇ : t ≥ 65  := by
                linarith
            have h₈ : t ^ 4 ≥ 65 ^ 4 := by
                exact Nat.pow_le_pow_of_le_left (by linarith) 4
            have h₉ : 65 ^ 4 > x ^ 3 := by
                have h₁₀ : x ≤ 64 := by
                    by_contra! h₁₁
                    have h₁₂ : x ≥ 65  := by
                        linarith
                    have h₁₃ : x ^ 3 ≥ 65 ^ 3 := by
                        exact Nat.pow_le_pow_of_le_left (by linarith) 3
                    have h₁₄ : 65 ^ 3 > 65 ^ 4 := by
                        norm_num
                        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
                        sorry
                    nlinarith
                have h₁₅ : x ^ 3 ≤ 64 ^ 3 := by
                    exact Nat.pow_le_pow_of_le_left (by linarith) 3
                norm_num at h₅ ⊢
                <;> nlinarith
            nlinarith
        have h₇ : x ≤ 84 := by
            by_contra! h
            have h₈ : x ≥ 85  := by
                linarith
            have h₉ : x ^ 3 ≥ 85 ^ 3 := by
                exact Nat.pow_le_pow_of_le_left (by linarith) 3
            have h₁₀ : 85 ^ 3 > t ^ 4 := by
                have h₁₁ : t ≤ 64  := by
                    linarith
                have h₁₂ : t ^ 4 ≤ 64 ^ 4 := by
                    exact Nat.pow_le_pow_of_le_left (by linarith) 4
                norm_num at h₅ ⊢
        
                try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
                sorry
            nlinarith
        interval_cases t <;> norm_num at h₅ ⊢ <;>
        (try omega) <;>
        (try {
            interval_cases x <;> norm_num at h₅ ⊢ <;> omega
        }) <;>
        (try {
            interval_cases x <;> norm_num at h₅ ⊢ <;> omega
        }) <;>
        (try {
            omega
        })
        <;>
        (try {
            nlinarith
        })
        <;>
        (try {
            ring_nf at h₅ ⊢
            omega
        })
    exact h_main