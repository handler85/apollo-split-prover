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
theorem induction_12dvd4expnp1p20 (n : ℕ) : 12 ∣ 4 ^ (n + 1) + 20 := by
  have h_main : 12 ∣ 4 ^ (n + 1) + 20 := by
    apply Nat.dvd_of_mod_eq_zero
    have h : (4 ^ (n + 1) + 20) % 12 = 0 := by
      have h₁ : (4 ^ (n + 1) + 20) % 3 = 0 := by
        rw [← Nat.mod_add_div (4 ^ (n + 1)) 3]
        simp [pow_add, pow_mul, Nat.pow_mod, Nat.mul_mod, Nat.add_mod]
        <;> induction n with
        | zero => norm_num
        | succ n ih =>
          simp [pow_add, pow_mul, Nat.pow_mod, Nat.mul_mod, Nat.add_mod, Nat.mod_mod] at ih ⊢
          <;> omega
      have h₂ : (4 ^ (n + 1) + 20) % 4 = 0 := by
        rw [← Nat.mod_add_div (4 ^ (n + 1)) 4]
        simp [pow_add, pow_mul, Nat.pow_mod, Nat.mul_mod, Nat.add_mod]
        <;> induction n with
        | zero => norm_num
        | succ n ih =>
          simp [pow_add, pow_mul, Nat.pow_mod, Nat.mul_mod, Nat.add_mod, Nat.mod_mod] at ih ⊢
          <;> omega
      have h₃ : (4 ^ (n + 1) + 20) % 12 = 0 := by
        omega
      exact h₃
    exact h
  exact h_main