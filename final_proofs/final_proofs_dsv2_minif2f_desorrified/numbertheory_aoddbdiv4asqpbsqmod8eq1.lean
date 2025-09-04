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
theorem numbertheory_aoddbdiv4asqpbsqmod8eq1 (a : ℤ) (b : ℕ) (h₀ : Odd a) (h₁ : 4 ∣ b) :
    (a ^ 2 + b ^ 2) % 8 = 1 := by
    have h_a_sq_mod_8 : (a ^ 2) % 8 = 1 := by
        have h₂ : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by
            cases' h₀ with k hk
            have h₃ : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by
                omega
            exact h₃
        rcases h₂ with (h₂ | h₂ | h₂ | h₂) <;>
        simp [h₂, pow_two, Int.mul_emod, Int.add_emod, Int.emod_emod]
        <;>
        (try omega) <;>
        (try norm_num) <;>
        (try ring_nf) <;>
        (try omega)
        <;>
        (try
            {
                omega
            })
        <;>
        (try
            {
                norm_num at *
                <;>
                omega
            })
    have h_b_sq_mod_8 : (b ^ 2 : ℤ) % 8 = 0 := by
        have h₂ : 4 ∣ b  := by
      
            gcongr
        have h₃ : b % 4 = 0 := by
            omega
        have h₄ : (b : ℤ) % 8 = 0 ∨ (b : ℤ) % 8 = 4 := by
            have h₅ : (b : ℤ) % 4 = 0  := by
                omega
            omega
        rcases h₄ with (h₄ | h₄)
        · -- Case: b % 8 = 0
            have h₅ : ((b : ℤ) ^ 2) % 8 = 0 := by
                have h₅₁ : (b : ℤ) % 8 = 0  := by
                    omega
                have h₅₂ : ((b : ℤ) ^ 2) % 8 = 0 := by
                    simp [h₅₁, pow_two, Int.mul_emod, Int.emod_emod]
                exact h₅₂
            exact_mod_cast h₅
        · -- Case: b % 8 = 4
            have h₅ : ((b : ℤ) ^ 2) % 8 = 0 := by
                have h₅₁ : (b : ℤ) % 8 = 4  := by
                    omega
                have h₅₂ : ((b : ℤ) ^ 2) % 8 = 0 := by
                    simp [h₅₁, pow_two, Int.mul_emod, Int.emod_emod]
                    <;> norm_num <;> omega
                exact h₅₂
            exact_mod_cast h₅
    have h_main : (a ^ 2 + b ^ 2) % 8 = 1 := by
        have h₃ : (a ^ 2 + b ^ 2 : ℤ) % 8 = 1 := by
            have h₄ : (a ^ 2 : ℤ) % 8 = 1  := by
        
                gcongr
            have h₅ : (b ^ 2 : ℤ) % 8 = 0  := by
        
                gcongr
            have h₆ : ((a ^ 2 + b ^ 2 : ℤ) % 8) = 1 := by
                omega
            exact_mod_cast h₆
        exact_mod_cast h₃
    exact h_main