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
lemma mathd_numbertheory_296_2
    (n : ℕ)
    (h₀ : (2 : ℕ) ≤ n)
    (x t : ℕ)
    (h₄ : t ^ (4 : ℕ) = n)
    (h₅ : x ^ (3 : ℕ) = n)
    (h : (84 : ℕ) < x)
    (h₈ : (85 : ℕ) ≤ x)
    (h₉ : (614125 : ℕ) ≤ n)
    (h₁₁ : t ≤ (64 : ℕ))
    (h₁₂ : n ≤ (16777216 : ℕ)) :
    n < (614125 : ℕ) := by
    have h_false : False := by
        have h₁₃ : x ≥ 85 := by
            linarith
        have h₁₄ : x ^ 3 ≥ 85 ^ 3 := by
            exact Nat.pow_le_pow_of_le_left h₁₃ 3
        have h₁₅ : n ≥ 614125 := by
            have h₁₅₁ : x ^ 3 = n := by
                linarith
            have h₁₅₂ : n ≥ 614125 := by
                linarith
            linarith
        have h₁₆ : n < 614125 := by
            try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
            try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
            sorry
        linarith
    have h_main : n < (614125 : ℕ) := by
        exfalso
        exact h_false
    exact h_main