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
theorem algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3 (a b c : ℝ) (h₀ : a ≤ b ∧ b ≤ c)
    (h₁ : a + b + c = 2) (h₂ : a * b + b * c + c * a = 1) :
    0 ≤ a ∧ a ≤ 1 / 3 ∧ 1 / 3 ≤ b ∧ b ≤ 1 ∧ 1 ≤ c ∧ c ≤ 4 / 3 := by
    have bc_expr : b * c = 1 - a * (2 - a)  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith



        have h_sum_bc : b + c = 2 - a := by
          have h₃ : a + b + c = 2 := h₁
          linarith

        have h_main : b * c = (1 : ℝ) - a * ((2 : ℝ) - a) := by
          have h₃ : a * b + b * c + c * a = 1 := h₂
          have h₄ : b * c = 1 - a * (b + c) := by
            -- Use the given condition to find a relationship involving b * c
            have h₅ : a * b + b * c + c * a = 1 := h₂
            have h₆ : b * c = 1 - a * (b + c) := by
              -- Use linear arithmetic to simplify the equation
              nlinarith
            exact h₆
          have h₅ : b * c = 1 - a * ((2 : ℝ) - a) := by
            -- Substitute the value of b + c from the given condition
            have h₆ : b + c = 2 - a := h_sum_bc
            rw [h₆] at h₄
            linarith
          exact h₅

        exact h_main


    have disc : 4 * a - 3 * a^2 ≥ 0  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith



        have h_main : a ^ (2 : ℕ) * (3 : ℝ) ≤ a * (4 : ℝ) := by
          have h₃ : a ≤ 1 / 2 := by
            nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (b - a), sq_nonneg (c - b),
              sq_nonneg (b - 1 / 2), sq_nonneg (c - 1 / 2)]
          have h₄ : a ≤ 4 / 3 := by
            nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (b - a), sq_nonneg (c - b),
              sq_nonneg (b - 1 / 2), sq_nonneg (c - 1 / 2)]
          have h₅ : a ^ (2 : ℕ) * (3 : ℝ) ≤ a * (4 : ℝ) := by
            have h₆ : a ^ 2 * 3 ≤ a * 4 := by
              nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (a - 4 / 3),
                sq_nonneg (a - 1), sq_nonneg (a + 1)]
            norm_num at h₆ ⊢
            <;> nlinarith
          exact h₅
        exact h_main


    have a_nonneg : 0 ≤ a  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith



        have h_main : 0 ≤ a := by
          by_contra h
          have h₃ : a < 0 := by linarith
          have h₄ : a ^ (2 : ℕ) * (3 : ℝ) ≤ a * (4 : ℝ) := disc
          have h₅ : a ^ 2 * 3 ≤ a * 4 := by
            norm_num at h₄ ⊢
            <;> nlinarith
          nlinarith [sq_nonneg (a - 4 / 3), sq_nonneg (a + 4 / 3), sq_nonneg (a - 2), sq_nonneg (a + 2)]
        exact h_main




    have a_bound : a ≤ 1 / 3  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith



        have h_main : a ≤ (1 / 3 : ℝ) := by
          norm_num [pow_two, pow_three] at disc h₂ bc_expr ⊢
          nlinarith [sq_nonneg (a - 1 / 3), sq_nonneg (b - 1 / 3), sq_nonneg (c - 1 / 3),
            mul_nonneg a_nonneg (sub_nonneg.mpr h₀.1), mul_nonneg a_nonneg (sub_nonneg.mpr h₀.2),
            mul_nonneg a_nonneg (sub_nonneg.mpr h₀.1), mul_nonneg a_nonneg (sub_nonneg.mpr h₀.2),
            mul_nonneg (sub_nonneg.mpr h₀.1) (sub_nonneg.mpr h₀.2),
            mul_nonneg (sub_nonneg.mpr h₀.1) a_nonneg, mul_nonneg (sub_nonneg.mpr h₀.2) a_nonneg]

        exact h_main


    have b_lower : 1 / 3 ≤ b  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith



        have h_main : (1 / 3 : ℝ) ≤ b := by
          have h₃ : b * c = 1 - a * 2 + a ^ 2 := by
            simpa [pow_two] using bc_expr
          have h₄ : c = 2 - a - b := by linarith
          rw [h₄] at h₃
          nlinarith [sq_nonneg (a - 1 / 3), sq_nonneg (b - 1 / 3), sq_nonneg (b - a),
            mul_nonneg a_nonneg (sub_nonneg.mpr a_bound), mul_nonneg (sub_nonneg.mpr a_bound) (sub_nonneg.mpr a_bound),
            mul_nonneg (sub_nonneg.mpr a_bound) a_nonneg, sq_nonneg (a - 1 / 3),
            mul_nonneg a_nonneg (sub_nonneg.mpr a_bound), mul_nonneg (sub_nonneg.mpr a_bound) a_nonneg]
        exact h_main


    have b_upper : b ≤ 1  := by
        linarith
    have c_lower : 1 ≤ c  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith



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





        have h_final : (1 : ℝ) ≤ c := by
            have h₃ : (4 / 3 : ℝ) ≤ c := by
                gcongr
            have h₄ : (1 : ℝ) ≤ c := by
                linarith
            exact h₄
        exact h_final

    have c_upper : c ≤ 4 / 3  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith



        have h_c_bound : c ≤ (4 / 3 : ℝ) := by
          have h₃ : c = 2 - a - b := by linarith
          have h₄ : c ≤ (4 / 3 : ℝ) := by
            rw [h₃]
            nlinarith [a_nonneg, a_bound, b_lower, b_upper, c_lower, sq_nonneg (a - 1 / 3),
              sq_nonneg (b - 1 / 3)]
          exact h₄
        exact h_c_bound


    exact try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
    
