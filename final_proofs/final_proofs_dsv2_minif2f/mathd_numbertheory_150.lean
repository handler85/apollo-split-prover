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
theorem mathd_numbertheory_150 (n : ℕ) (h₀ : ¬Nat.Prime (7 + 30 * n)) : 6 ≤ n := by
  have h_main : 6 ≤ n := by
    by_contra! h
    have h₁ : n ≤ 5  := by
      linarith
    have h₂ : n ≤ 5  := by
      linarith
    interval_cases n <;> norm_num [Nat.Prime] at h₀ ⊢ <;>
    (try contradiction) <;>
    (try norm_num) <;>
    (try decide) <;>
    (try
      {
        norm_num [Nat.Prime] at h₀ ⊢
        <;>
        (try contradiction) <;>
        (try decide)
      }) <;>
    (try
      {
        simp_all [Nat.Prime]
        <;>
        norm_num at *
        <;>
        omega
      })
    <;>
    (try
      {
        norm_num [Nat.Prime] at h₀ ⊢
        <;>
        (try contradiction) <;>
        (try decide)
      })
    <;>
    (try
      {
        simp_all [Nat.Prime]
        <;>
        norm_num at *
        <;>
        omega
      })
  exact h_main