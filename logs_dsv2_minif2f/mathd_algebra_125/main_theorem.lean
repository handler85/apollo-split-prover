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
theorem mathd_algebra_125 (x y : ℕ) (h₀ : 0 < x ∧ 0 < y) (h₁ : 5 * x = y)
    (h₂ : ↑x - (3 : ℤ) + (y - (3 : ℤ)) = 30) : x = 6 := by
  have h_main : x = 6 := by
    have h₃ : y = 5 * x  := by
      omega
    have h₄ : (x : ℤ) - 3 + (y - 3) = 30  := by
      simpa [h₃] using h₂
    have h₅ : x ≤ 36 := by
      by_contra! h
      have h₆ : x ≥ 37  := by
        omega
      have h₇ : (x : ℤ) ≥ 37  := by
        exact_mod_cast h₆
      have h₈ : (y : ℤ) = 5 * (x : ℤ) := by
        simp [h₃]
        <;> ring_nf
        <;> omega
      have h₉ : (x : ℤ) - 3 + (y - 3) = 30  := by
        simpa [h₃] using h₂
      have h₁₀ : (x : ℤ) - 3 + (y - 3) = 30  := by
        simpa [h₃] using h₂
      nlinarith
    interval_cases x <;> norm_num at h₄ ⊢ <;>
    (try omega) <;>
    (try
      {
        simp_all [h₃]
        <;> omega
      }) <;>
    (try
      {
        ring_nf at h₄ ⊢
        <;> omega
      })
    <;>
    omega
  exact h_main