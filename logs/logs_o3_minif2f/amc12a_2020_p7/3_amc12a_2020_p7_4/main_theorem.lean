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

lemma amc12a_2020_p7_4
  (a : ℕ → ℕ)
  (h₅ : a (5 : ℕ) ^ (3 : ℕ) = (216 : ℕ))
  (h₆ : a (6 : ℕ) ^ (3 : ℕ) = (343 : ℕ))
  (ha0 : a (0 : ℕ) = (1 : ℕ))
  (ha1 : a (1 : ℕ) = (2 : ℕ))
  (ha2 : a (2 : ℕ) = (3 : ℕ))
  (ha3 : a (3 : ℕ) = (4 : ℕ))
  (ha4 : a (4 : ℕ) = (5 : ℕ)) :
  a (5 : ℕ) = (6 : ℕ) := by
  have h₇ : a (5 : ℕ) ≤ 6 := by
    by_contra h
    have h₇ : a (5 : ℕ) ≥ 7 := by omega
    have h₈ : a (5 : ℕ) ^ (3 : ℕ) ≥ 7 ^ (3 : ℕ) := by
      have h₉ : a (5 : ℕ) ≥ 7 := by omega
      have h₁₀ : a (5 : ℕ) ^ (3 : ℕ) ≥ 7 ^ (3 : ℕ) := by
        exact Nat.pow_le_pow_of_le_left h₉ 3
      exact h₁₀
    have h₉ : 7 ^ (3 : ℕ) > 216 := by norm_num
    have h₁₀ : a (5 : ℕ) ^ (3 : ℕ) > 216 := by omega
    omega
  
  have h₈ : a (5 : ℕ) ≥ 6 := by
    by_contra h
    have h₉ : a (5 : ℕ) ≤ 5 := by omega
    have h₁₀ : a (5 : ℕ) ^ (3 : ℕ) ≤ 5 ^ (3 : ℕ) := by
      exact Nat.pow_le_pow_of_le_left h₉ 3
    have h₁₁ : 5 ^ (3 : ℕ) = 125 := by norm_num
    have h₁₂ : a (5 : ℕ) ^ (3 : ℕ) ≤ 125 := by
      omega
    have h₁₃ : a (5 : ℕ) ^ (3 : ℕ) = 216 := h₅
    omega
  
  have h₉ : a (5 : ℕ) = 6 := by
    have h₁₀ : a (5 : ℕ) ≤ 6 := h₇
    have h₁₁ : a (5 : ℕ) ≥ 6 := h₈
    have h₁₂ : a (5 : ℕ) = 6 := by
      omega
    exact h₁₂
  
  simpa using h₉
