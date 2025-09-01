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
lemma imo_1981_p6_1
    (f : ℕ → ℕ → ℕ)
    (h₀ : ∀ (y : ℕ), f (0 : ℕ) y = y + (1 : ℕ))
    (h₁ : ∀ (x : ℕ), f (x + (1 : ℕ)) (0 : ℕ) = f x (1 : ℕ))
    (h₂ : ∀ (x y : ℕ), f ((1 : ℕ) + x) ((1 : ℕ) + y) = f x (f ((1 : ℕ) + x) y)) :
    ∀ (y : ℕ), f (3 : ℕ) (f (4 : ℕ) y) = (2 : ℕ) ^ f (4 : ℕ) y * (8 : ℕ) - (3 : ℕ) := by
        (try omega) <;>
        (try
            {
                simp [h₀, h₁, h₂, Nat.pow_succ, Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib, Nat.add_sub_assoc] at h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ h₁₃ h₁₄ h₁₅ h₁₆ h₁₇ h₁₈ h₁₉ h₂₀ h₂₁ h₂₂ h₂₃ h₂₄ h₂₅ h₂₆ h₂₇ h₂₈ ⊢
                <;> omega
            }) <;>
        (try
            {
                cases y <;> simp_all [h₀, h₁, h₂, Nat.pow_succ, Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib, Nat.add_sub_assoc]
                <;> ring_nf at *
                <;> omega
            }) <;>
        (try
            {
                aesop
            })
        <;>
        (try
            {
                omega
            })
        <;>
        (try
            {
                nlinarith
            })
        intro
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
        sorry