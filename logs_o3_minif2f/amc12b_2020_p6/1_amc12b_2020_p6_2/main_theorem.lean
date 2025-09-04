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
lemma amc12b_2020_p6_2
    (n! : ℝ)
    (n : ℕ)
    (h₀ : (9 : ℕ) ≤ n)
    (factorization : True)
    (fact2 : (↑((1 : ℕ) + n)! : ℝ) = (↑n : ℝ) * n! + n!)
    (fact1 : (↑((2 : ℕ) + n)! : ℝ) = (↑n : ℝ) * n! * (3 : ℝ) + (↑n : ℝ) ^ (2 : ℕ) * n! + n! * (2 : ℝ)) :
    (↑n : ℝ) * n! * n!⁻¹ * (2 : ℝ) + (↑n : ℝ) ^ (2 : ℕ) * n! * n!⁻¹ + n! * n!⁻¹ =
        (1 : ℝ) + (↑n : ℝ) * (2 : ℝ) + (↑n : ℝ) ^ (2 : ℕ) := by
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
        sorry
    exact h_final