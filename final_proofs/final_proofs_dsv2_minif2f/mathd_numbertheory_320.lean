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
theorem mathd_numbertheory_320 (n : ℕ) (h₀ : n < 101) (h₁ : 101 ∣ 123456 - n) : n = 34 := by
    have h_main : n = 34 := by
        have h₂ : n ≤ 100  := by
            linarith
        have h₃ : 101 ∣ 123456 - n  := by
      
            gcongr
        have h₄ : n ≤ 123456 := by
            by_contra h
            have h₅ : n ≥ 123457  := by
                omega
            have h₆ : 123456 - n = 0 := by
                have h₇ : n ≥ 123457  := by
                    omega
                have h₈ : 123456 < n  := by
                    omega
                have h₉ : 123456 - n = 0 := by
                    omega
                exact h₉
            rw [h₆] at h₃
            norm_num at h₃
            <;> omega
        interval_cases n <;> norm_num at h₃ ⊢ <;>
        (try omega) <;>
        (try {
            norm_num at h₃
            <;> omega
        }) <;>
        (try {
            omega
        }) <;>
        (try {
            simp_all [Nat.dvd_iff_mod_eq_zero]
            <;> omega
        })
    exact h_main