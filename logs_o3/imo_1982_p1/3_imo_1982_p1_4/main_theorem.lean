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
lemma imo_1982_p1_4
  (f : ℕ → ℕ)
  (h₀ :
  ∀ (m n : ℕ)
    (0 : ℕ) < m ∧ (0 : ℕ) < n →
      (↑(f (m + n)) : ℤ) - (↑(f m) : ℤ) - (↑(f n) : ℤ) = (0 : ℤ) ∨ f (m + n) - f m - f n = (1 : ℕ))
  (h₁ : f (2 : ℕ) = (0 : ℕ))
  (h₂ : (0 : ℕ) < f (3 : ℕ))
  (h₃ : f (9999 : ℕ) = (3333 : ℕ))
  (h_f1 : f (1 : ℕ) = (0 : ℕ))
  (h_f3 : f (3 : ℕ) = (1 : ℕ))
  (add_three : ∀ (n : ℕ), f (n + (3 : ℕ)) = f n + (1 : ℕ)) :
  ∀ (n : ℕ), f n = n / (3 : ℕ) := by
  try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
  sorry