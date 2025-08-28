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
lemma algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3_6
    (a b c : ℝ)
    (h₀ : a ≤ b ∧ b ≤ c)
    (h₁ : a + b + c = (2 : ℝ))
    (a_nonneg : (0 : ℝ) ≤ a)
    (b_upper : b ≤ (1 : ℝ))
    (b_lower : (1 / 3 : ℝ) ≤ b)
    (a_bound : a ≤ (1 / 3 : ℝ))
    (disc : a ^ (2 : ℕ) * (3 : ℝ) ≤ a * (4 : ℝ))
    (bc_expr : b * c = (1 : ℝ) - a * (2 : ℝ) + a ^ (2 : ℕ))
    (h₂ : (1 : ℝ) - a * (2 : ℝ) + a * b + a * c + a ^ (2 : ℕ) = (1 : ℝ)) :
    (1 : ℝ) ≤ c := by
    have h_c_lower : (4 / 3 : ℝ) ≤ c := by
        have h₃ : c = 2 - a - b := by
            linarith
        rw [h₃]
        have h₄ : a ≤ 1 / 3 := by
            gcongr
        have h₅ : 0 ≤ a := by
            gcongr
        have h₆ : 1 / 3 ≤ b := by
            gcongr
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
        sorry
    have h_final : (1 : ℝ) ≤ c := by
        have h₃ : (4 / 3 : ℝ) ≤ c := by
            gcongr
        have h₄ : (1 : ℝ) ≤ c := by
            linarith
        exact h₄
    exact h_final