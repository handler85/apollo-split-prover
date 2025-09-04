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

lemma induction_12dvd4expnp1p20_3
  (n : ℕ)
  (ih : (12 : ℕ) ∣ (4 : ℕ) ^ (n + (1 : ℕ)) + (20 : ℕ)) :
  (4 : ℕ) ^ (n + (2 : ℕ)) + (20 : ℕ) = (4 : ℕ) * ((4 : ℕ) ^ (n + (1 : ℕ)) + (20 : ℕ)) - (60 : ℕ) := by
  have h_main : (4 : ℕ) ^ (n + (2 : ℕ)) + (20 : ℕ) = (4 : ℕ) * ((4 : ℕ) ^ (n + (1 : ℕ)) + (20 : ℕ)) - (60 : ℕ) := by
    have h₁ : (4 : ℕ) ^ (n + (2 : ℕ)) = 4 * (4 ^ (n + 1)) := by
      rw [show n + 2 = n + 1 + 1 by ring]
      rw [pow_add]
      <;> ring
      <;> simp [pow_succ]
      <;> ring
    rw [h₁]
    cases n with
    | zero =>
      norm_num
    | succ n =>
      simp [pow_add, pow_one, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.mul_zero, Nat.zero_add] at *
      <;> ring_nf at *
      <;> omega
  
  exact h_main
