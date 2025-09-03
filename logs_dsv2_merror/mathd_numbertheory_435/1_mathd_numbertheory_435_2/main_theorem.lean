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
lemma mathd_numbertheory_435_2
  (h₀ : (0 : ℕ) < (4 : ℕ))
  (h₁ : ∀ (n : ℕ), ((6 : ℕ) * n + (4 : ℕ)).gcd ((6 : ℕ) * n + (3 : ℕ)) = (1 : ℕ))
  (h₂ : ∀ (n : ℕ), ((6 : ℕ) * n + (4 : ℕ)).gcd ((6 : ℕ) * n + (2 : ℕ)) = (1 : ℕ))
  (h : (4 : ℕ) < (5 : ℕ))
  (h₄ : (4 : ℕ) ≤ (4 : ℕ))
  (h₃ : ∀ (n : ℕ), ((4 : ℕ) + n * (6 : ℕ)).gcd ((1 : ℕ) + n * (6 : ℕ)) = (1 : ℕ)) :
  False := by
  have h_false : False := by
    have h₅ := h₂ 0
    have h₆ := h₂ 1
    have h₇ := h₂ 2
    have h₈ := h₂ 3
    have h₉ := h₂ 4
    norm_num at h₅ h₆ h₇ h₈ h₉
    <;>
    (try contradiction) <;>
    (try omega) <;>
    (try
      {
        simp_all [Nat.gcd_eq_right, Nat.gcd_eq_left]
        <;>
        omega
      })
    <;>
    aesop
  exact h_false
