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

lemma mathd_numbertheory_277_1
  (m n : ℕ)
  (h₀ : m.gcd n = (6 : ℕ))
  (h₁ : m.lcm n = (126 : ℕ))
  (h₂ : m * n = (756 : ℕ))
  (h₄ : m ∣ (756 : ℕ))
  (h₅ : n ∣ (756 : ℕ)) :
  m ≤ (756 : ℕ) := by
  have h_main : m ≤ (756 : ℕ) := by
    have h₆ : m ∣ 756 := h₄
    have h₇ : m ≤ 756 := Nat.le_of_dvd (by norm_num) h₆
    exact h₇
  exact h_main
