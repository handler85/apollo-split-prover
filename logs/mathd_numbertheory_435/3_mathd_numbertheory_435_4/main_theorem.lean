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

lemma mathd_numbertheory_435_4
  (k : ℕ)
  (h₀ : (0 : ℕ) < k)
  (h₁ : ∀ (n : ℕ), ((6 : ℕ) * n + k).gcd ((6 : ℕ) * n + (3 : ℕ)) = (1 : ℕ))
  (h₂ : ∀ (n : ℕ), ((6 : ℕ) * n + k).gcd ((6 : ℕ) * n + (2 : ℕ)) = (1 : ℕ))
  (h_gcd_k3 : k.gcd (3 : ℕ) = (1 : ℕ))
  (h_gcd_k2 : Odd k)
  (k_odd : k % (2 : ℕ) = (1 : ℕ))
  (h₃ : ∀ (n : ℕ), (n * (6 : ℕ) + k).gcd ((1 : ℕ) + n * (6 : ℕ)) = (1 : ℕ)) :
  ¬k % (3 : ℕ) = (0 : ℕ) := by
  have h_main : ¬k % (3 : ℕ) = (0 : ℕ) := by
    intro h
    have h₄ : 3 ∣ k := by
      omega
    have h₅ : k.gcd 3 = 3 := by
      have h₅₁ : 3 ∣ k := h₄
      have h₅₂ : k.gcd 3 = 3 := by
        have h₅₃ : 3 ∣ k := h₅₁
        have h₅₄ : k.gcd 3 = 3 := by
          rw [Nat.gcd_comm]
          rw [Nat.gcd_comm]
          simp_all [Nat.gcd_eq_right, Nat.dvd_gcd]
          <;> omega
        exact h₅₄
      exact h₅₂
    have h₆ : k.gcd 3 = 1 := h_gcd_k3
    omega
  exact h_main
