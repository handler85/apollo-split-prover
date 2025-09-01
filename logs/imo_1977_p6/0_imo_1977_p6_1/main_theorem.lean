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
lemma imo_1977_p6_1
  (case h)
  (f : ℕ → ℕ)
  (h₀ : ∀ (n : ℕ), (0 : ℕ) < f n)
  (h₁ : ∀ (n : ℕ), (0 : ℕ) < n → f (f n) < f (n + (1 : ℕ)))
  (hn✝ : (0 : ℕ) < n✝)
  (n : ℕ)
  (ih : ∀ m < n, (0 : ℕ) < m → f m = m)
  (hn : (0 : ℕ) < n) :
  f n = n := by
  try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
  sorry