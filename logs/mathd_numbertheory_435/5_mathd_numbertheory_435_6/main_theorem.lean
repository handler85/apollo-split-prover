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
lemma mathd_numbertheory_435_6
  (k : ℕ)
  (h₀ : (0 : ℕ) < k)
  (h₁ : ∀ (n : ℕ), ((6 : ℕ) * n + k).gcd ((6 : ℕ) * n + (3 : ℕ)) = (1 : ℕ))
  (h₂ : ∀ (n : ℕ), ((6 : ℕ) * n + k).gcd ((6 : ℕ) * n + (2 : ℕ)) = (1 : ℕ))
  (h_gcd_k3 : k.gcd (3 : ℕ) = (1 : ℕ))
  (h_gcd_k2 : Odd k)
  (k_odd : k % (2 : ℕ) = (1 : ℕ))
  (k_not_div3 : ¬k % (3 : ℕ) = (0 : ℕ))
  (hk : k < (5 : ℕ))
  (case1 : ¬k = (1 : ℕ))
  (case2 : ¬k = (2 : ℕ))
  (case3 : ¬k = (3 : ℕ))
  (case4 : ¬k = (4 : ℕ))
  (h₃ : ∀ (n : ℕ), (n * (6 : ℕ) + k).gcd ((1 : ℕ) + n * (6 : ℕ)) = (1 : ℕ)) :
  (5 : ℕ) ≤ k := by
  have h_k_cases : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by
    have h₄ : k < 5 := by assumption
    have h₅ : k > 0 := by linarith
    interval_cases k <;> norm_num at * <;> simp_all (config := {decide := true})
    <;> omega
  
  have h_false : False := by
    rcases h_k_cases with (rfl | rfl | rfl | rfl)
    · -- Case k = 1
      have h₆ := h₁ 0
      have h₇ := h₁ 1
      have h₈ := h₁ 2
      have h₉ := h₂ 0
      have h₁₀ := h₂ 1
      have h₁₁ := h₂ 2
      have h₁₂ := h₃ 0
      have h₁₃ := h₃ 1
      have h₁₄ := h₃ 2
      norm_num at h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ h₁₃ h₁₄ <;>
        (try contradiction) <;>
        (try omega) <;>
        (try simp_all [Nat.gcd_eq_right, Nat.gcd_eq_left, Nat.odd_iff_not_even, Nat.even_iff] <;> omega) <;>
        aesop
    · -- Case k = 2
      have h₆ := h₁ 0
      have h₇ := h₁ 1
      have h₈ := h₁ 2
      have h₉ := h₂ 0
      have h₁₀ := h₂ 1
      have h₁₁ := h₂ 2
      have h₁₂ := h₃ 0
      have h₁₃ := h₃ 1
      have h₁₄ := h₃ 2
      norm_num at h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ h₁₃ h₁₄ <;>
        (try contradiction) <;>
        (try omega) <;>
        (try simp_all [Nat.gcd_eq_right, Nat.gcd_eq_left, Nat.odd_iff_not_even, Nat.even_iff] <;> omega) <;>
        aesop
    · -- Case k = 3
      have h₆ := h₁ 0
      have h₇ := h₁ 1
      have h₈ := h₁ 2
      have h₉ := h₂ 0
      have h₁₀ := h₂ 1
      have h₁₁ := h₂ 2
      have h₁₂ := h₃ 0
      have h₁₃ := h₃ 1
      have h₁₄ := h₃ 2
      norm_num at h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ h₁₃ h₁₄ <;>
        (try contradiction) <;>
        (try omega) <;>
        (try simp_all [Nat.gcd_eq_right, Nat.gcd_eq_left, Nat.odd_iff_not_even, Nat.even_iff] <;> omega) <;>
        aesop
    · -- Case k = 4
      have h₆ := h₁ 0
      have h₇ := h₁ 1
      have h₈ := h₁ 2
      have h₉ := h₂ 0
      have h₁₀ := h₂ 1
      have h₁₁ := h₂ 2
      have h₁₂ := h₃ 0
      have h₁₃ := h₃ 1
      have h₁₄ := h₃ 2
      norm_num at h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ h₁₃ h₁₄ <;>
        (try contradiction) <;>
        (try omega) <;>
        (try simp_all [Nat.gcd_eq_right, Nat.gcd_eq_left, Nat.odd_iff_not_even, Nat.even_iff] <;> omega) <;>
        aesop
  
  have h_main : (5 : ℕ) ≤ k := by
    exfalso
    exact h_false
  
  exact h_main
