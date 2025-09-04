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

lemma mathd_algebra_158_5
  (a : ℕ)
  (h₀ : Even a)
  (h₁ :
  (↑(∑ k ∈ Finset.range (8 : ℕ), ((2 : ℕ) * k + (1 : ℕ))) : ℤ) -
      (↑(∑ k ∈ Finset.range (5 : ℕ), (a + (2 : ℕ) * k)) : ℤ) =
    (4 : ℤ))
  (h_sum_odd : ∑ k ∈ Finset.range (8 : ℕ), ((2 : ℕ) * k + (1 : ℕ)) = (64 : ℕ))
  (h_sum_even : ∑ k ∈ Finset.range (5 : ℕ), (a + (2 : ℕ) * k) = (5 : ℕ) * a + (20 : ℕ))
  (h_equation : (64 : ℕ) - ((5 : ℕ) * a + (20 : ℕ)) = (4 : ℕ))
  (h_simplified : (44 : ℕ) - (5 : ℕ) * a = (4 : ℕ)) :
  (5 : ℕ) * a = (40 : ℕ) := by
  have h_main : (5 : ℕ) * a = (40 : ℕ) := by
    have h₂ : (44 : ℕ) - (5 : ℕ) * a = (4 : ℕ) := h_simplified
    have h₃ : (5 : ℕ) * a ≤ 44 := by
      by_contra h
      have h₄ : (5 : ℕ) * a ≥ 45 := by omega
      have h₅ : (44 : ℕ) - (5 : ℕ) * a = 0 := by
        have h₆ : (5 : ℕ) * a ≥ 45 := by omega
        have h₇ : (44 : ℕ) - (5 : ℕ) * a = 0 := by
          omega
        exact h₇
      omega
    have h₄ : (5 : ℕ) * a = 40 := by
      have h₅ : (44 : ℕ) - (5 : ℕ) * a = (4 : ℕ) := h_simplified
      have h₆ : (5 : ℕ) * a ≤ 44 := by omega
      interval_cases (5 : ℕ) * a <;> norm_num at h₅ ⊢ <;> omega
    exact h₄
  exact h_main
