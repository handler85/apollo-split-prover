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

lemma mathd_numbertheory_711_3
  (m n a b : ℕ)
  (h₀ : (0 : ℕ) < a ∧ (0 : ℕ) < b)
  (hb : n = b * (8 : ℕ))
  (ha : m = a * (8 : ℕ))
  (h₂ : (a * (8 : ℕ)).lcm (b * (8 : ℕ)) = (112 : ℕ))
  (h₁ : (a * (8 : ℕ)).gcd (b * (8 : ℕ)) = (8 : ℕ)) :
  a.gcd b = (1 : ℕ) := by
  have h_main : a.gcd b = 1 := by
    have h₃ : (a * 8).gcd (b * 8) = 8 := by simpa [mul_comm] using h₁
    have h₄ : (a * 8).gcd (b * 8) = 8 * (a.gcd b) := by
      rw [← Nat.gcd_mul_left]
      <;> simp [mul_comm]
    rw [h₄] at h₃
    have h₅ : 8 * (a.gcd b) = 8 := by linarith
    have h₆ : a.gcd b = 1 := by
      apply Nat.eq_of_mul_eq_mul_left (show 0 < 8 by norm_num)
      linarith
    exact h₆
  exact h_main
