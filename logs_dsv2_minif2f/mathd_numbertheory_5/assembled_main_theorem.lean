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
theorem mathd_numbertheory_5 (n : ℕ) (h₀ : 10 ≤ n) (h₁ : ∃ x, x ^ 2 = n) (h₂ : ∃ t, t ^ 3 = n) :
    64 ≤ n := by
    have h_main : 64 ≤ n := by
        by_contra! h
        have h₃ : n ≤ 63  := by
            linarith
        have h₄ : ∃ x, x ^ 2 = n  := by
      
            gcongr
        have h₅ : ∃ t, t ^ 3 = n  := by
      
            gcongr
        rcases h₄ with ⟨x, hx⟩
        rcases h₅ with ⟨t, ht⟩
        have h₆ : x ^ 2 ≤ 63  := by
            linarith
        have h₇ : t ^ 3 ≤ 63  := by
            linarith
        have h₈ : x ≤ 7 := by
            nlinarith
        have h₉ : t ≤ 4 := by
            nlinarith [pow_two_nonneg t, pow_two_nonneg (t - 1), pow_two_nonneg (t + 1)]
        interval_cases x <;> interval_cases t <;> norm_num at hx ht ⊢ <;>
            (try omega) <;>
            (try {
                nlinarith
            }) <;>
            (try {
                aesop
            }) <;>
            (try {
                simp_all [pow_two, pow_three]
                <;> nlinarith
            })
        <;>
        (try {
            omega
        })
        <;>
        (try {
            aesop
        })
        <;>
        (try {
            simp_all [pow_two, pow_three]
            <;> nlinarith
        })
    exact h_main