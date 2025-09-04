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
theorem mathd_numbertheory_234 (a b : ℕ) (h₀ : 1 ≤ a ∧ a ≤ 9 ∧ b ≤ 9)
    (h₁ : (10 * a + b) ^ 3 = 912673) : a + b = 16 := by
    have h_main : a = 9 ∧ b = 7 := by
        have h₂ : a ≤ 9  := by
            linarith
        have h₃ : b ≤ 9  := by
            linarith
        have h₄ : 1 ≤ a  := by
            linarith
        have h₅ : a ≤ 9  := by
            linarith
        have h₆ : b ≤ 9  := by
            linarith
        have h₇ : a ≥ 1  := by
            linarith
        interval_cases a <;> interval_cases b <;> norm_num at h₁ ⊢ <;>
            (try omega) <;> (try
                {
                    ring_nf at h₁
                    norm_num at h₁
                    <;> omega
                }) <;> (try
                {
                    simp_all [pow_three]
                    <;> ring_nf at h₁ ⊢
                    <;> norm_num at h₁ ⊢
                    <;> omega
                })
        <;> omega
    have h_final : a + b = 16 := by
        have h₂ : a = 9  := by
      
            linarith
        have h₃ : b = 7  := by
      
            linarith
        subst_vars
        <;> norm_num
        <;> linarith
    exact h_final