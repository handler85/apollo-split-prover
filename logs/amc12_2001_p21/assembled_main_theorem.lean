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
theorem amc12_2001_p21 (a b c d : ℕ) (h₀ : a * b * c * d = 8!) (h₁ : a * b + a + b = 524)
    (h₂ : b * c + b + c = 146) (h₃ : c * d + c + d = 104) : ↑a - ↑d = (10 : ℤ) := by
    have h_main : a = 24 ∧ b = 20 ∧ c = 6 ∧ d = 14 := by
        have h₄ : a * b * c * d = 40320 := by
            norm_num [Nat.factorial] at h₀ ⊢
            <;> linarith
        have h₅ : a * b + a + b = 524  := by
      
            gcongr
        have h₆ : b * c + b + c = 146  := by
      
            gcongr
        have h₇ : c * d + c + d = 104  := by
      
            gcongr
        have h₈ : a > 0 := by
            by_contra h
            simp_all [Nat.mul_eq_zero, Nat.add_eq_zero_iff]
            <;> nlinarith
        have h₉ : b > 0 := by
            by_contra h
            simp_all [Nat.mul_eq_zero, Nat.add_eq_zero_iff]
            <;> nlinarith
        have h₁₀ : c > 0 := by
            by_contra h
            simp_all [Nat.mul_eq_zero, Nat.add_eq_zero_iff]
            <;> nlinarith
        have h₁₁ : d > 0 := by
            by_contra h
            simp_all [Nat.mul_eq_zero, Nat.add_eq_zero_iff]
            <;> nlinarith
        have h₁₂ : a * b ≤ 524 := by
            nlinarith
        have h₁₃ : b * c ≤ 146 := by
            nlinarith
        have h₁₄ : c * d ≤ 104 := by
            nlinarith
        have h₁₅ : a ≤ 524 := by
            nlinarith
        have h₁₆ : b ≤ 146 := by
            nlinarith
        have h₁₇ : c ≤ 104 := by
            nlinarith
        have h₁₈ : d ≤ 104 := by
            nlinarith
        have h₁₉ : a = 24 ∧ b = 20 ∧ c = 6 ∧ d = 14 := by
            have h₂₀ : a ∣ 40320 := by
                use b * c * d
                linarith
            have h₂₁ : b ∣ 40320 := by
                use a * c * d
                linarith
            have h₂₂ : c ∣ 40320 := by
                use a * b * d
                linarith
            have h₂₃ : d ∣ 40320 := by
                use a * b * c
                linarith
            have h₂₄ : a = 24 ∧ b = 20 ∧ c = 6 ∧ d = 14 := by
                have h₂₅ : a ≤ 524  := by
                    nlinarith
                have h₂₆ : b ≤ 146  := by
                    nlinarith
                have h₂₇ : c ≤ 104  := by
                    nlinarith
                have h₂₈ : d ≤ 104  := by
                    nlinarith
                interval_cases a <;> norm_num at h₂₀ ⊢ <;>
                    (try omega) <;>
                    (try {
                        interval_cases b <;> norm_num at h₂₁ ⊢ <;>
                            (try omega) <;>
                            (try {
                                interval_cases c <;> norm_num at h₂₂ ⊢ <;>
                                    (try omega) <;>
                                    (try {
                                        interval_cases d <;> norm_num at h₂₃ ⊢ <;>
                                            (try omega) <;>
                                            (try {
                                                norm_num at h₀ h₁ h₂ h₃ ⊢ <;>
                                                omega
                                            })
                                    })
                            })
                    }) <;>
                    (try {
                        omega
                    }) <;>
                    (try {
                        aesop
                    })
            exact h₂₄
        exact h₁₉
    have h_final : ↑a - ↑d = (10 : ℤ) := by
        rcases h_main with ⟨rfl, rfl, rfl, rfl⟩
        norm_num
        <;> rfl
    exact h_final