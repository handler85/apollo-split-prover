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
theorem mathd_numbertheory_521 (m n : ℕ) (h₀ : Even m) (h₁ : Even n) (h₂ : m - n = 2)
    (h₃ : m * n = 288) : m = 18 := by
    have h_main : m = 18 := by
        have h₄ : m ≥ n := by
            by_contra h
            have h₅ : m < n  := by
                omega
            have h₆ : m - n = 0 := by
                have h₇ : m ≤ n  := by
                    omega
                have h₈ : m - n = 0 := by
                    omega
                exact h₈
            omega
        have h₅ : m = n + 2 := by
            have h₅₁ : m ≥ n  := by
        
                gcongr
            have h₅₂ : m - n = 2  := by
        
                gcongr
            have h₅₃ : m = n + 2 := by
                omega
            exact h₅₃
        rw [h₅] at h₃
        have h₆ : (n + 2) * n = 288 := by
            simpa using h₃
        have h₇ : n ≤ 18 := by
            by_contra h
            have h₈ : n ≥ 19  := by
                omega
            have h₉ : (n + 2) * n ≥ 19 * 19 := by
                have h₁₀ : n ≥ 19  := by
                    omega
                have h₁₁ : (n + 2) * n ≥ 19 * 19 := by
                    nlinarith
                exact h₁₁
            nlinarith
        interval_cases n <;> norm_num at h₆ ⊢ <;>
        (try omega) <;>
        (try {
            omega
            exact h₈
        }) <;>
        (try {
            omega
        })
    exact h_main