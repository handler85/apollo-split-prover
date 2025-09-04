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
theorem mathd_numbertheory_430 (a b c : ℕ)
  (h₀ : 1 ≤ a ∧ a ≤ 9) (h₁ : 1 ≤ b ∧ b ≤ 9) (h₂ : 1 ≤ c ∧ c ≤ 9)
  (h₃ : a ≠ b) (h₄ : a ≠ c) (h₅ : b ≠ c)
  (h₆ : a + b = c)
  (h₇ : 10 * a + a - b = 2 * c)
  (h₈ : c * b = 10 * a + a + a) : a + b + c = 8 := by
  have h_b_eq : b = c - a := by
    omega
  have h_subst : 11 * a - (c - a) = 2 * c := by
    omega
  have h_c_eq : c = 4 * a := by
    omega
  have h_b_val : b = 3 * a := by
    linarith
  have h_eq : 12 * a * a = 12 * a := by
    simp_all only [tsub_le_iff_right, ne_eq, mul_eq_mul_right_iff, OfNat.ofNat_ne_zero, not_false_eq_true, mul_eq_left₀]
  have h_a : a = 1 := by
    simp_all only [tsub_le_iff_right, ne_eq, mul_eq_mul_right_iff, OfNat.ofNat_ne_zero, not_false_eq_true, mul_eq_left₀]
  have h_b_final : b = 3 := by
    linarith
  have h_c_final : c = 4 := by
    linarith
  have h_sum : a + b + c = 8 := by
    linarith
  exact h_sum