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
  (h₁ : m.lcm n = (126 : ℕ)) :
  m * n = (756 : ℕ) := by
  have h_main : m * n = 756 := by
    have h₂ : m.gcd n * m.lcm n = m * n := by
      rw [Nat.gcd_mul_lcm]
    rw [h₀, h₁] at h₂
    norm_num at h₂ ⊢
    <;> nlinarith
  exact h_main
