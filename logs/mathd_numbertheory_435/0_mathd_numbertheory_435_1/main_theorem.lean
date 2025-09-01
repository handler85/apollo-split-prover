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
lemma mathd_numbertheory_435_1
  (h₀ : (0 : ℕ) < (2 : ℕ))
  (h₁ : ∀ (n : ℕ), ((6 : ℕ) * n + (2 : ℕ)).gcd ((6 : ℕ) * n + (3 : ℕ)) = (1 : ℕ))
  (h₂ : ∀ (n : ℕ), ((6 : ℕ) * n + (2 : ℕ)).gcd ((6 : ℕ) * n + (2 : ℕ)) = (1 : ℕ))
  (h : (2 : ℕ) < (5 : ℕ))
  (h₄ : (2 : ℕ) ≤ (4 : ℕ))
  (h₃ : ∀ (n : ℕ), ((2 : ℕ) + n * (6 : ℕ)).gcd ((1 : ℕ) + n * (6 : ℕ)) = (1 : ℕ)) :
  False := by
  have h₅ : False := by
    have h₆ := h₂ 0
    norm_num [Nat.gcd_eq_right] at h₆
    <;> contradiction
  exact h₅
