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

lemma amc12b_2020_p6_2_2
  (n! : ℝ)
  (n : ℕ)
  (h₀ : (9 : ℕ) ≤ n)
  (fact2 : (↑((1 : ℕ) + n)! : ℝ) = (↑n : ℝ) * n! + n!)
  (fact1 : (↑((2 : ℕ) + n)! : ℝ) = (↑n : ℝ) * n! * (3 : ℝ) + (↑n : ℝ) ^ (2 : ℕ) * n! + n! * (2 : ℝ))
  (h_main : (0 : ℝ) < n!)
  (h₁ : n! * n!⁻¹ = (1 : ℝ)) :
  (1 : ℝ) + (↑n : ℝ) * n! * n!⁻¹ * (2 : ℝ) + (↑n : ℝ) ^ (2 : ℕ) * n! * n!⁻¹ =
    (1 : ℝ) + (↑n : ℝ) * (2 : ℝ) + (↑n : ℝ) ^ (2 : ℕ) := by
  have h_main_goal : (1 : ℝ) + (↑n : ℝ) * n! * n!⁻¹ * (2 : ℝ) + (↑n : ℝ) ^ (2 : ℕ) * n! * n!⁻¹ = (1 : ℝ) + (↑n : ℝ) * (2 : ℝ) + (↑n : ℝ) ^ (2 : ℕ) := by
    have h₂ : n! * n!⁻¹ = 1 := by
      linarith
    have h₃ : (↑n : ℝ) * n! * n!⁻¹ = (↑n : ℝ) * 1 := by
      have h₄ : n! * n!⁻¹ = 1 := by linarith
      have h₅ : (↑n : ℝ) * n! * n!⁻¹ = (↑n : ℝ) * (n! * n!⁻¹) := by ring
      rw [h₅]
      rw [h₄]
      <;> ring
    have h₄ : (↑n : ℝ) ^ (2 : ℕ) * n! * n!⁻¹ = (↑n : ℝ) ^ (2 : ℕ) * 1 := by
      have h₅ : n! * n!⁻¹ = 1 := by linarith
      have h₆ : (↑n : ℝ) ^ (2 : ℕ) * n! * n!⁻¹ = (↑n : ℝ) ^ (2 : ℕ) * (n! * n!⁻¹) := by ring
      rw [h₆]
      rw [h₅]
      <;> ring
    simp_all [mul_assoc]
    <;> ring_nf
    <;> nlinarith
  exact h_main_goal
