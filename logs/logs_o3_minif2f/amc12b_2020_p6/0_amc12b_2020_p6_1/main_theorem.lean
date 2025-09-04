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
lemma amc12b_2020_p6_1
    (n! : ℝ)
    (n : ℕ)
    (h₀ : (9 : ℕ) ≤ n)
    (fact1 : (↑(n + (2 : ℕ))! : ℝ) = ((↑n : ℝ) + (2 : ℝ)) * ((↑n : ℝ) + (1 : ℝ)) * n!) :
    (↑(n + (1 : ℕ))! : ℝ) = ((↑n : ℝ) + (1 : ℝ)) * n! := by
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