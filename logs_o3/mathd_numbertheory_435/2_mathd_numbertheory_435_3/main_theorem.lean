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

lemma mathd_numbertheory_435_3
  (k : ℕ)
  (h₀ : (0 : ℕ) < k)
  (h₁ : ∀ (n : ℕ), ((6 : ℕ) * n + k).gcd ((6 : ℕ) * n + (3 : ℕ)) = (1 : ℕ))
  (h₂ : ∀ (n : ℕ), ((6 : ℕ) * n + k).gcd ((6 : ℕ) * n + (2 : ℕ)) = (1 : ℕ))
  (h_gcd_k3 : k.gcd (3 : ℕ) = (1 : ℕ))
  (h_gcd_k2 : Odd k)
  (h₃ : ∀ (n : ℕ), (n * (6 : ℕ) + k).gcd ((1 : ℕ) + n * (6 : ℕ)) = (1 : ℕ)) :
  k % (2 : ℕ) = (1 : ℕ) := by
  have h_main : k % (2 : ℕ) = (1 : ℕ) := by
    cases' h_gcd_k2 with t ht
    have h₄ := ht
    simp at h₄
    have h₅ := h₄
    omega
  exact h_main
