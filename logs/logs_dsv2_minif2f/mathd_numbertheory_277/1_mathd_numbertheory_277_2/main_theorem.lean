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

lemma mathd_numbertheory_277_2
  (m n : ℕ)
  (h₀ : m.gcd n = (6 : ℕ))
  (h₁ : m.lcm n = (126 : ℕ))
  (h₂ : m * n = (756 : ℕ))
  (h₄ : m ∣ (756 : ℕ))
  (h₅ : n ∣ (756 : ℕ))
  (h₆ : m ≤ (756 : ℕ)) :
  n ≤ (756 : ℕ) := by
  have h_main : n ≤ (756 : ℕ) := by
    have h₇ : n ∣ 756 := by simpa using h₅
    have h₈ : n ≤ 756 := Nat.le_of_dvd (by norm_num) h₇
    exact h₈
  exact h_main
