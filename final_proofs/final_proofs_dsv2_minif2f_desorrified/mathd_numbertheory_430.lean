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
theorem mathd_numbertheory_430 (a b c : ℕ) (h₀ : 1 ≤ a ∧ a ≤ 9) (h₁ : 1 ≤ b ∧ b ≤ 9)
    (h₂ : 1 ≤ c ∧ c ≤ 9) (h₃ : a ≠ b) (h₄ : a ≠ c) (h₅ : b ≠ c) (h₆ : a + b = c)
    (h₇ : 10 * a + a - b = 2 * c) (h₈ : c * b = 10 * a + a + a) : a + b + c = 8 := by
  have h_main : a = 1 ∧ b = 3 ∧ c = 4 := by
    have h₉ : a ≤ 9  := by
      linarith
    have h₁₀ : b ≤ 9  := by
      linarith
    have h₁₁ : c ≤ 9  := by
      linarith
    have h₁₂ : a ≥ 1  := by
      linarith
    have h₁₃ : b ≥ 1  := by
      linarith
    have h₁₄ : c ≥ 1  := by
      linarith
    interval_cases a <;> interval_cases b <;> interval_cases c <;> norm_num at h₆ h₇ h₈ h₃ h₄ h₅ ⊢ <;>
      (try omega) <;> (try {
        simp_all [mul_comm, mul_assoc, mul_left_comm]
        <;> ring_nf at *
        <;> omega
      }) <;> (try {
        aesop
      }) <;> (try {
        omega
      })
    <;> aesop
  have h_sum : a + b + c = 8 := by
    rcases h_main with ⟨rfl, rfl, rfl⟩
    <;> norm_num
    <;> aesop
  exact h_sum