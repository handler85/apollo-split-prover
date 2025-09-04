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

lemma mathd_numbertheory_711_4
  (m n a b : ℕ)
  (h₀ : (0 : ℕ) < a ∧ (0 : ℕ) < b)
  (coprime_ab : a.gcd b = (1 : ℕ))
  (ab_eq : a * b = (14 : ℕ))
  (m_times_n : a * b * (64 : ℕ) = (896 : ℕ))
  (hb : n = b * (8 : ℕ))
  (ha : m = a * (8 : ℕ))
  (h₂ : (a * (8 : ℕ)).lcm (b * (8 : ℕ)) = (112 : ℕ))
  (h₁ : (a * (8 : ℕ)).gcd (b * (8 : ℕ)) = (8 : ℕ)) :
  (9 : ℕ) ≤ a + b := by
  have h_sum_ge_nine : 9 ≤ a + b := by
    have h₁ : a ∣ 14 := by
      use b
      linarith
    have h₂ : b ∣ 14 := by
      use a
      linarith
    have h₃ : a ≤ 14 := Nat.le_of_dvd (by norm_num) h₁
    have h₄ : b ≤ 14 := Nat.le_of_dvd (by norm_num) h₂
    interval_cases a <;> interval_cases b <;> norm_num at * <;>
    (try contradiction) <;>
    (try simp_all [Nat.gcd_eq_right, Nat.lcm, Nat.gcd_eq_left]) <;>
    (try omega) <;>
    (try
      {
        simp_all [Nat.gcd_eq_right, Nat.lcm, Nat.gcd_eq_left]
        <;> norm_num at *
        <;> omega
      }) <;>
    (try
      {
        aesop
      })
    <;>
    omega
  exact h_sum_ge_nine
