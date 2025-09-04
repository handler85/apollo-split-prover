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

lemma algebra_amgm_sumasqdivbgeqsuma_1
  (a b c d : ℝ)
  (h₀ : (0 : ℝ) < a ∧ (0 : ℝ) < b ∧ (0 : ℝ) < c ∧ (0 : ℝ) < d) :
  (2 : ℝ) * a ≤ a ^ (2 : ℕ) / b + b := by
  have h₁ : (2 : ℝ) * a ≤ a ^ (2 : ℕ) / b + b := by
    have h₂ : 0 < b := h₀.2.1
    have h₃ : 0 < a := h₀.1
    have h₄ : 0 < a ^ (2 : ℕ) := by positivity
    have h₅ : 0 < b := by linarith
    have h₆ : 0 < a * b := by positivity
    -- Use the fact that (a - b)^2 ≥ 0 to prove the inequality
    have h₇ : (a - b) ^ 2 ≥ 0 := by nlinarith
    have h₈ : a ^ (2 : ℕ) / b + b ≥ 2 * a := by
      have h₉ : a ^ (2 : ℕ) / b + b = a ^ 2 / b + b := by norm_num
      rw [h₉]
      field_simp [h₂.ne']
      rw [le_div_iff (by positivity)]
      -- Use nlinarith to prove the inequality
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - b * 2)]
    linarith
  exact h₁
