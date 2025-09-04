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

lemma mathd_numbertheory_711_2
  (m n : ℕ)
  (h₀ : (0 : ℕ) < m ∧ (0 : ℕ) < n)
  (h₁ : m.gcd n = (8 : ℕ))
  (h₂ : m.lcm n = (112 : ℕ))
  (div_m : (8 : ℕ) ∣ m) :
  (8 : ℕ) ∣ n := by
  have h_main : (8 : ℕ) ∣ n := by
    have h₃ : 8 ∣ n := by
      have h₄ : 8 ∣ m := by simpa [Nat.dvd_iff_mod_eq_zero] using div_m
      have h₅ : 8 ∣ n := by
        have h₆ : 8 ∣ Nat.gcd m n := by simpa [h₁] using h₄
        have h₇ : 8 ∣ n := by
          -- Use the property that gcd(m, n) divides both m and n.
          have h₈ : 8 ∣ Nat.gcd m n := by simpa [h₁] using h₆
          have h₉ : Nat.gcd m n ∣ n := Nat.gcd_dvd_right m n
          exact Nat.dvd_trans h₈ h₉
        exact h₇
      exact h₅
    exact h₃
  exact h_main
