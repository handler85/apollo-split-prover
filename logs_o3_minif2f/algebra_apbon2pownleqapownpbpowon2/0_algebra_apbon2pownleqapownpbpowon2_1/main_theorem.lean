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
lemma algebra_apbon2pownleqapownpbpowon2_1
    (a b : ℝ)
    (n : ℕ)
    (h₀ : (0 : ℝ) < a ∧ (0 : ℝ) < b)
    (h₁ : (0 : ℕ) < n)
    (f : ℝ → ℝ := fun (x : ℝ) => x ^ n) :
    f ((a + b) / (2 : ℝ)) ≤ (f a + f b) / (2 : ℝ) := by
    have h_main : ((a + b) / 2 : ℝ) ^ n ≤ (a ^ n + b ^ n) / 2 := by
        have h₂ : 0 < a := by
            linarith
        have h₃ : 0 < b := by
            linarith
        have h₄ : 0 < a * b := by
            positivity
        have h₅ : 0 < a * b := by
            positivity
        have h₆ : ((a + b) / 2 : ℝ) ^ n ≤ (a ^ n + b ^ n) / 2 := by
            have h₇ : ∀ n : ℕ, 0 < n → ((a + b) / 2 : ℝ) ^ n ≤ (a ^ n + b ^ n) / 2 := by
                intro n hn
                induction' hn with n hn IH
                · 
                    norm_num
                    <;>
                    nlinarith [sq_nonneg (a - b)]
                · 
                    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
                    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
                    sorry
            exact h₇ n h₁
        gcongr
    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
    sorry