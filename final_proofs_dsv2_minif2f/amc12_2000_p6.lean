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
theorem amc12_2000_p6 (p q : ℕ) (h₀ : Nat.Prime p ∧ Nat.Prime q) (h₁ : 4 ≤ p ∧ p ≤ 18)
    (h₂ : 4 ≤ q ∧ q ≤ 18) : ↑p * ↑q - (↑p + ↑q) ≠ (194 : ℕ) := by
  have h_main : ↑p * ↑q - (↑p + ↑q) ≠ (194 : ℕ) := by
    have h₃ : p ≤ 18  := by
      linarith
    have h₄ : q ≤ 18  := by
      linarith
    have h₅ : p ≥ 4  := by
      linarith
    have h₆ : q ≥ 4  := by
      linarith
    have h₇ : p ≤ 18  := by
      linarith
    have h₈ : q ≤ 18  := by
      linarith
    have h₉ : p ≥ 4  := by
      linarith
    have h₁₀ : q ≥ 4  := by
      linarith
    interval_cases p <;> interval_cases q <;> norm_num [Nat.Prime] at h₀ ⊢ <;>
      (try contradiction) <;>
      (try omega) <;>
      (try
        {
          norm_num at *
          <;>
          (try contradiction) <;>
          (try omega)
        }) <;>
      (try
        {
          simp_all [Nat.Prime]
          <;>
          norm_num at *
          <;>
          (try contradiction) <;>
          (try omega)
        })
    <;>
    (try
      {
        norm_num at *
        <;>
        (try contradiction) <;>
        (try omega)
      })
    <;>
    (try
      {
        simp_all [Nat.Prime]
        <;>
        norm_num at *
        <;>
        (try contradiction) <;>
        (try omega)
      })
  exact h_main