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
lemma mathd_numbertheory_435_2
    (k : ℕ)
    (h₀ : (0 : ℕ) < k)
    (h₁ : ∀ (n : ℕ), ((6 : ℕ) * n + k).gcd ((6 : ℕ) * n + (3 : ℕ)) = (1 : ℕ))
    (h₂ : ∀ (n : ℕ), ((6 : ℕ) * n + k).gcd ((6 : ℕ) * n + (2 : ℕ)) = (1 : ℕ))
    (h₃ : ∀ (n : ℕ), ((6 : ℕ) * n + k).gcd ((6 : ℕ) * n + (1 : ℕ)) = (1 : ℕ))
    (h_gcd_k3 : k.gcd (3 : ℕ) = (1 : ℕ)) :
    Odd k := by
    have h_main : Odd k := by
        rw [Nat.odd_iff_not_even]
        intro h_even
        have h₅ : k % 2 = 0 := by
            exact even_iff.mp h_even
        have h₆ : (k : ℕ).gcd 2 = 2 := by
            have h₇ : 2 ∣ k := by
                omega
            have h₈ : (k : ℕ).gcd 2 = 2 := by
                have h₉ : 2 ∣ k := by
                    gcongr
                have h₁₀ : (k : ℕ).gcd 2 = 2 := by
                    rw [Nat.gcd_comm]
                    rw [← Nat.mod_add_div k 2]
                    simp [h₉, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
                    <;>
                    simp_all [Nat.gcd_eq_right]
                    <;>
                    omega
                exact h₁₀
            exact h₈
        <;> omega
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
        sorry
    exact h_main