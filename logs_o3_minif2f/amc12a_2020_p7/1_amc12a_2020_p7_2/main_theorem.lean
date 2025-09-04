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

lemma amc12a_2020_p7_2
  (a : ℕ → ℕ)
  (h₃ : a (3 : ℕ) ^ (3 : ℕ) = (64 : ℕ))
  (h₄ : a (4 : ℕ) ^ (3 : ℕ) = (125 : ℕ))
  (h₅ : a (5 : ℕ) ^ (3 : ℕ) = (216 : ℕ))
  (h₆ : a (6 : ℕ) ^ (3 : ℕ) = (343 : ℕ))
  (ha0 : a (0 : ℕ) = (1 : ℕ))
  (ha1 : a (1 : ℕ) = (2 : ℕ))
  (ha2 : a (2 : ℕ) = (3 : ℕ)) :
  a (3 : ℕ) = (4 : ℕ) := by
  have h_main : a (3 : ℕ) = (4 : ℕ) := by
    have h7 : a (3 : ℕ) ^ 3 = 64 := h₃
    have h8 : a (3 : ℕ) ≤ 6 := by
      by_contra h
      have h9 : a (3 : ℕ) ≥ 7 := by
        omega
      have h10 : a (3 : ℕ) ^ 3 ≥ 7 ^ 3 := by
        exact Nat.pow_le_pow_of_le_left (by omega) 3
      have h11 : 7 ^ 3 = 343 := by norm_num
      have h12 : a (3 : ℕ) ^ 3 ≥ 343 := by
        omega
      omega
    interval_cases a (3 : ℕ) <;> norm_num at h7 ⊢ <;>
    (try omega) <;> (try
      {
        simp_all [pow_three]
        <;> ring_nf at *
        <;> omega
      }) <;> (try
      {
        omega
      })
    <;> omega
  
  exact h_main
