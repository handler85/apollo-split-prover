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

lemma amc12a_2020_p7_3
  (a : ℕ → ℕ)
  (h₄ : a (4 : ℕ) ^ (3 : ℕ) = (125 : ℕ))
  (h₅ : a (5 : ℕ) ^ (3 : ℕ) = (216 : ℕ))
  (h₆ : a (6 : ℕ) ^ (3 : ℕ) = (343 : ℕ))
  (ha0 : a (0 : ℕ) = (1 : ℕ))
  (ha1 : a (1 : ℕ) = (2 : ℕ))
  (ha2 : a (2 : ℕ) = (3 : ℕ))
  (ha3 : a (3 : ℕ) = (4 : ℕ)) :
  a (4 : ℕ) = (5 : ℕ) := by
  have h_main : a (4 : ℕ) = (5 : ℕ) := by
    have h₇ : a (4 : ℕ) ^ (3 : ℕ) = (125 : ℕ) := h₄
    have h₈ : a (4 : ℕ) ≤ 5 := by
      by_contra! h
      have h₉ : a (4 : ℕ) ≥ 6 := by omega
      have h₁₀ : a (4 : ℕ) ^ (3 : ℕ) ≥ 6 ^ (3 : ℕ) := by
        exact Nat.pow_le_pow_of_le_left (by omega) 3
      have h₁₁ : 6 ^ (3 : ℕ) = 216 := by norm_num
      have h₁₂ : a (4 : ℕ) ^ (3 : ℕ) ≥ 216 := by
        omega
      omega
    have h₉ : a (4 : ℕ) ≥ 5 := by
      by_contra! h
      have h₁₀ : a (4 : ℕ) ≤ 4 := by omega
      have h₁₁ : a (4 : ℕ) ^ (3 : ℕ) ≤ 4 ^ (3 : ℕ) := by
        exact Nat.pow_le_pow_of_le_left h₁₀ 3
      have h₁₂ : 4 ^ (3 : ℕ) = 64 := by norm_num
      have h₁₃ : a (4 : ℕ) ^ (3 : ℕ) ≤ 64 := by
        omega
      omega
    have h₁₀ : a (4 : ℕ) = 5 := by
      interval_cases a (4 : ℕ) <;> norm_num at h₇ ⊢ <;>
        (try omega) <;>
        (try { contradiction }) <;>
        (try { linarith })
    exact h₁₀
  exact h_main
