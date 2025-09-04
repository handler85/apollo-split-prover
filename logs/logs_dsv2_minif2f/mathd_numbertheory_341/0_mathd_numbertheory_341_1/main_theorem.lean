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

lemma mathd_numbertheory_341_1
  (a b c : ℕ)
  (h₀ : a ≤ (9 : ℕ) ∧ b ≤ (9 : ℕ) ∧ c ≤ (9 : ℕ))
  (h₁ : (5 : ℕ) = c ∧ (2 : ℕ) = b ∧ (6 : ℕ) = a) :
  a + b + c = (13 : ℕ) := by
  have h_main : a + b + c = 13 := by
    have h₂ : a = 6 := by
      linarith [h₁.2.2]
    have h₃ : b = 2 := by
      linarith [h₁.2.1]
    have h₄ : c = 5 := by
      linarith [h₁.1]
    subst_vars
    <;> norm_num
    <;> linarith
  exact h_main
