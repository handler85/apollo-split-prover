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

lemma algebra_sqineq_unitcircatbpamblt1_1
  (a b : ℝ)
  (h₀ : a ^ (2 : ℕ) + b ^ (2 : ℕ) = (1 : ℝ))
  (abs_a_le_one : |a| ≤ (1 : ℝ))
  (abs_b_le_one : |b| ≤ (1 : ℝ))
  (a_le_one : a ≤ (1 : ℝ))
  (b_ge_neg_one : (-1 : ℝ) ≤ b)
  (right_nonneg : (0 : ℝ) ≤ (1 : ℝ) + b)
  (rewrite_expr : True) :
  (-1 : ℝ) + a + (a * b - b) ≤ (0 : ℝ) := by
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
