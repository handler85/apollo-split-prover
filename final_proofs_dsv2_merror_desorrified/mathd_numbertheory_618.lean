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
theorem mathd_numbertheory_618 (n : ℕ) (hn : n > 0) (p : ℕ → ℕ) (h₀ : ∀ x, p x = x ^ 2 - x + 41)
    (h₁ : 1 < Nat.gcd (p n) (p (n + 1))) : 41 ≤ n := by
  have h_main : 41 ≤ n := by
    by_contra! h
    have h₂ : n ≤ 40  := by
      linarith
    have h₃ : n ≥ 1  := by
      linarith
    have h₄ : p n = n ^ 2 - n + 41  := by
      simp [h₀]
    have h₅ : p (n + 1) = (n + 1) ^ 2 - (n + 1) + 41  := by
      simp [h₀]
    have h₆ : Nat.gcd (p n) (p (n + 1)) = 1 := by
      interval_cases n <;> norm_num [h₄, h₅, Nat.gcd_eq_right, Nat.gcd_eq_left] <;>
        (try decide) <;>
        (try
          {
            simp_all [Nat.gcd_eq_right, Nat.gcd_eq_left]
            <;> norm_num
            <;> rfl
          }) <;>
        (try
          {
            ring_nf at *
            <;> norm_num at *
            <;> omega
          }) <;>
        (try
          {
            simp_all [Nat.gcd_eq_right, Nat.gcd_eq_left]
            <;> norm_num
            <;> rfl
          })
    linarith
  exact h_main