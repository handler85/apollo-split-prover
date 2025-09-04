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

lemma amc12a_2020_p7_1
  (a : ℕ → ℕ)
  (h₁ : a (1 : ℕ) ^ (3 : ℕ) = (8 : ℕ))
  (h₂ : a (2 : ℕ) ^ (3 : ℕ) = (27 : ℕ))
  (h₃ : a (3 : ℕ) ^ (3 : ℕ) = (64 : ℕ))
  (h₄ : a (4 : ℕ) ^ (3 : ℕ) = (125 : ℕ))
  (h₅ : a (5 : ℕ) ^ (3 : ℕ) = (216 : ℕ))
  (h₆ : a (6 : ℕ) ^ (3 : ℕ) = (343 : ℕ))
  (ha0 : a (0 : ℕ) = (1 : ℕ)) :
  a (1 : ℕ) = (2 : ℕ) := by
  have h_main : a 1 = 2 := by
    have h₁' : a 1 ^ 3 = 8 := by simpa using h₁
    have h₂' : a 1 = 2 := by
      -- We know that 2^3 = 8, so a 1 must be 2
      have h₇ : a 1 ≤ 2 := by
        -- Prove that a 1 ≤ 2 by contradiction
        by_contra! h
        -- If a 1 > 2, then a 1 ≥ 3, which implies a 1 ^ 3 ≥ 27, contradicting a 1 ^ 3 = 8
        have h₈ : a 1 ≥ 3 := by omega
        have h₉ : a 1 ^ 3 ≥ 3 ^ 3 := by
          exact Nat.pow_le_pow_of_le_left (by omega) 3
        have h₁₀ : 3 ^ 3 = 27 := by norm_num
        have h₁₁ : a 1 ^ 3 ≥ 27 := by omega
        omega
      have h₈ : a 1 ≥ 1 := by
        by_contra! h
        have h₉ : a 1 = 0 := by omega
        rw [h₉] at h₁'
        norm_num at h₁'
        <;> simp_all
        <;> norm_num
        <;> nlinarith
      interval_cases a 1 <;> norm_num at h₁' ⊢ <;>
        (try omega) <;> (try contradiction) <;> (try aesop)
    exact h₂'
  exact h_main
