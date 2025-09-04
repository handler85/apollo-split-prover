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
theorem algebra_sqineq_unitcircatbpamblt1 (a b : ℝ) (h₀ : a ^ 2 + b ^ 2 = 1) : a * b + (a - b) ≤ 1 := by
  have rewrite_expr : a * b + (a - b) = 1 + (a - 1) * (b + 1) := by
    linarith
  have abs_a_le_one : |a| ≤ 1 := by
    exact le_of_max_le_left abs_a_le_one
  have abs_b_le_one : |b| ≤ 1 := by
    exact neg_le_of_abs_le abs_b_le_one
  have a_le_one : a ≤ 1 := by
    linarith
  have b_ge_neg_one : b ≥ -1 := by
    linarith
  have left_nonpos : a - 1 ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg left_nonpos right_nonneg
  have right_nonneg : b + 1 ≥ 0 := by
    linarith
  have prod_nonpos : (a - 1) * (b + 1) ≤ 0 := by
    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


    
    have h_main : (-1 : ℝ) + a + (a * b - b) = (a - 1) * (1 + b) := by
      ring_nf
      <;>
      (try norm_num) <;>
      (try linarith [abs_le.mp abs_a_le_one, abs_le.mp abs_b_le_one]) <;>
      (try nlinarith)
      <;>
      nlinarith [abs_le.mp abs_a_le_one, abs_le.mp abs_b_le_one, h₀, sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (a + 1), sq_nonneg (b + 1)]
    
    have h_final : (-1 : ℝ) + a + (a * b - b) ≤ (0 : ℝ) := by
      rw [h_main]
      have h₁ : a - 1 ≤ 0 := by
        nlinarith [abs_le.mp abs_a_le_one]
      have h₂ : 1 + b ≥ 0 := by nlinarith
      have h₃ : (a - 1) * (1 + b) ≤ 0 := by
        nlinarith
      nlinarith
    exact h_final


  rw [rewrite_expr]
  have final_step : 1 + (a - 1) * (b + 1) ≤ 1 := by
    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
  exact final_step