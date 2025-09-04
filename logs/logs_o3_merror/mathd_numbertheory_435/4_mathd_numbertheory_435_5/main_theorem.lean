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

lemma mathd_numbertheory_435_5
  (k : ℕ)
  (h₀ : (0 : ℕ) < k)
  (h₁ : ∀ (n : ℕ), ((6 : ℕ) * n + k).gcd ((6 : ℕ) * n + (3 : ℕ)) = (1 : ℕ))
  (h₂ : ∀ (n : ℕ), ((6 : ℕ) * n + k).gcd ((6 : ℕ) * n + (2 : ℕ)) = (1 : ℕ))
  (h_gcd_k3 : k.gcd (3 : ℕ) = (1 : ℕ))
  (h_gcd_k2 : Odd k)
  (k_odd : k % (2 : ℕ) = (1 : ℕ))
  (k_not_div3 : ¬k % (3 : ℕ) = (0 : ℕ))
  (hk : k < (5 : ℕ))
  (case1 : ¬k = (1 : ℕ))
  (case2 : ¬k = (2 : ℕ))
  (case3 : ¬k = (3 : ℕ))
  (h₃ : ∀ (n : ℕ), (n * (6 : ℕ) + k).gcd ((1 : ℕ) + n * (6 : ℕ)) = (1 : ℕ)) :
  ¬k = (4 : ℕ) := by
  have h_main : k ≠ 4 := by
    intro h
    have h₄ := h₂ 0
    simp [h, Nat.gcd_eq_right] at h₄
    <;> norm_num at h₄ <;> contradiction
  exact h_main
