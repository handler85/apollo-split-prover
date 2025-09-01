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
theorem mathd_numbertheory_314 (r n : ℕ) (h₀ : r = 1342 % 13) (h₁ : 0 < n) (h₂ : 1342 ∣ n)
    (h₃ : n % 13 < r) : 6710 ≤ n := by
    have h_r : r = 3 := by
        rw [h₀]
        <;> norm_num
        <;> rfl
    have h_main : 6710 ≤ n := by
        have h₄ : n % 13 < 3 := by
            rw [h_r] at h₃
            exact h₃
        have h₅ : 1342 ∣ n  := by
      
            gcongr
        have h₆ : n ≥ 6710 := by
            by_contra h
            have h₇ : n ≤ 6709  := by
                linarith
            have h₈ : n % 13 < 3  := by
        
                gcongr
            have h₉ : n % 13 = 0 ∨ n % 13 = 1 ∨ n % 13 = 2 := by
                omega
            have h₁₀ : 1342 ∣ n  := by
        
                gcongr
            have h₁₁ : n ≤ 6709  := by
                linarith
            have h₁₂ : n ≥ 1  := by
                linarith
            interval_cases n <;> norm_num [Nat.dvd_iff_mod_eq_zero] at h₁₀ h₈ h₉ <;>
                (try omega) <;> (try contradiction) <;> (try omega) <;> (try omega)
            <;>
                (try
                    {
                        omega
                    }) <;>
                (try
                    {
                        simp_all [Nat.mod_eq_of_lt]
                        <;> omega
                    })
        linarith
    exact h_main