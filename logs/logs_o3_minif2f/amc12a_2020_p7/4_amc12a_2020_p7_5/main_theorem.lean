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

lemma amc12a_2020_p7_5
  (a : ℕ → ℕ)
  (h₆ : a (6 : ℕ) ^ (3 : ℕ) = (343 : ℕ))
  (ha0 : a (0 : ℕ) = (1 : ℕ))
  (ha1 : a (1 : ℕ) = (2 : ℕ))
  (ha2 : a (2 : ℕ) = (3 : ℕ))
  (ha3 : a (3 : ℕ) = (4 : ℕ))
  (ha4 : a (4 : ℕ) = (5 : ℕ))
  (ha5 : a (5 : ℕ) = (6 : ℕ)) :
  a (6 : ℕ) = (7 : ℕ) := by
  have h_main : a (6 : ℕ) = 7 := by
    have h₇ : a (6) ^ 3 = 343 := h₆
    have h₈ : a (6) ≤ 9 := by
      by_contra! h
      have h₉ : a (6) ≥ 10 := by linarith
      have h₁₀ : a (6) ^ 3 ≥ 10 ^ 3 := by
        exact Nat.pow_le_pow_of_le_left (by linarith) 3
      nlinarith
    interval_cases a (6) <;> norm_num at h₇ ⊢ <;>
    (try contradiction) <;>
    (try omega) <;>
    (try
      {
        simp_all [pow_succ]
        <;> ring_nf at *
        <;> omega
      })
    <;>
    (try
      {
        nlinarith
      })
    <;>
    (try
      {
        omega
      })
  exact h_main
