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

lemma mathd_numbertheory_711_1
  (m n : ℕ)
  (h₀ : (0 : ℕ) < m ∧ (0 : ℕ) < n)
  (h₁ : m.gcd n = (8 : ℕ))
  (h₂ : m.lcm n = (112 : ℕ)) :
  (8 : ℕ) ∣ m := by
  have h_main : (8 : ℕ) ∣ m := by
    have h₃ : (m.gcd n : ℕ) ∣ m := Nat.gcd_dvd_left m n
    have h₄ : (m.gcd n : ℕ) = 8 := by simpa using h₁
    rw [h₄] at h₃
    exact h₃
  exact h_main
