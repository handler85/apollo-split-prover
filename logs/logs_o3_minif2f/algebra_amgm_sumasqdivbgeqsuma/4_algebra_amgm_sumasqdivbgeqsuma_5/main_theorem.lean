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

lemma algebra_amgm_sumasqdivbgeqsuma_5
  (a b c d : ℝ)
  (h₀ : (0 : ℝ) < a ∧ (0 : ℝ) < b ∧ (0 : ℝ) < c ∧ (0 : ℝ) < d)
  (sum_h :
  a * (2 : ℝ) + b * (2 : ℝ) + c * (2 : ℝ) + d * (2 : ℝ) ≤
    a + a ^ (2 : ℕ) * b⁻¹ + b + b ^ (2 : ℕ) * c⁻¹ + c + c ^ (2 : ℕ) * d⁻¹ + d + d ^ (2 : ℕ) * a⁻¹)
  (h4 : d * (2 : ℝ) ≤ a + d ^ (2 : ℕ) * a⁻¹)
  (h3 : c * (2 : ℝ) ≤ c ^ (2 : ℕ) * d⁻¹ + d)
  (h2 : b * (2 : ℝ) ≤ b ^ (2 : ℕ) * c⁻¹ + c)
  (h1 : a * (2 : ℝ) ≤ a ^ (2 : ℕ) * b⁻¹ + b) :
  a + b + c + d ≤ a ^ (2 : ℕ) * b⁻¹ + b ^ (2 : ℕ) * c⁻¹ + c ^ (2 : ℕ) * d⁻¹ + d ^ (2 : ℕ) * a⁻¹ := by
  have h_main : a + b + c + d ≤ a ^ (2 : ℕ) * b⁻¹ + b ^ (2 : ℕ) * c⁻¹ + c ^ (2 : ℕ) * d⁻¹ + d ^ (2 : ℕ) * a⁻¹ := by
    have h₁ : a * (2 : ℝ) ≤ a ^ (2 : ℕ) * b⁻¹ + b := h1
    have h₂ : b * (2 : ℝ) ≤ b ^ (2 : ℕ) * c⁻¹ + c := h2
    have h₃ : c * (2 : ℝ) ≤ c ^ (2 : ℕ) * d⁻¹ + d := h3
    have h₄ : d * (2 : ℝ) ≤ d ^ (2 : ℕ) * a⁻¹ + a := by
      have h₅ : d * (2 : ℝ) ≤ a + d ^ (2 : ℕ) * a⁻¹ := h4
      have h₆ : d * (2 : ℝ) ≤ d ^ (2 : ℕ) * a⁻¹ + a := by
        linarith
      exact h₆
    have h₅ : a + b + c + d ≤ a ^ (2 : ℕ) * b⁻¹ + b ^ (2 : ℕ) * c⁻¹ + c ^ (2 : ℕ) * d⁻¹ + d ^ (2 : ℕ) * a⁻¹ := by
      -- Sum the inequalities to get the desired result
      have h₆ : a * (2 : ℝ) + b * (2 : ℝ) + c * (2 : ℝ) + d * (2 : ℝ) ≤ a + a ^ (2 : ℕ) * b⁻¹ + b + b ^ (2 : ℕ) * c⁻¹ + c + c ^ (2 : ℕ) * d⁻¹ + d + d ^ (2 : ℕ) * a⁻¹ := sum_h
      have h₇ : 2 * (a + b + c + d) ≤ (a ^ (2 : ℕ) * b⁻¹ + b ^ (2 : ℕ) * c⁻¹ + c ^ (2 : ℕ) * d⁻¹ + d ^ (2 : ℕ) * a⁻¹) + (a + b + c + d) := by linarith
      have h₈ : a + b + c + d ≤ a ^ (2 : ℕ) * b⁻¹ + b ^ (2 : ℕ) * c⁻¹ + c ^ (2 : ℕ) * d⁻¹ + d ^ (2 : ℕ) * a⁻¹ := by
        linarith
      exact h₈
    exact h₅
  exact h_main
