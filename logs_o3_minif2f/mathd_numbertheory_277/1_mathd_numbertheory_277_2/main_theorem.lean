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
  (prod_eq : m * n = (756 : ℕ)) :
  ∃ (a : ℕ), m = a * (6 : ℕ) ∧ ∃ (x : ℕ), n = x * (6 : ℕ) ∧ a.gcd x = (1 : ℕ) := by
  try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
  try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
  sorry