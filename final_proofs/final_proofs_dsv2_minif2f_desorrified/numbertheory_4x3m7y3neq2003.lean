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
theorem numbertheory_4x3m7y3neq2003 (x y : ℤ) : 4 * x ^ 3 - 7 * y ^ 3 ≠ 2003 := by
    have h_main : 4 * x ^ 3 - 7 * y ^ 3 ≠ 2003 := by
        intro h
    
    
    
    
        have h₂ : x % 7 = 0 ∨ x % 7 = 1 ∨ x % 7 = 2 ∨ x % 7 = 3 ∨ x % 7 = 4 ∨ x % 7 = 5 ∨ x % 7 = 6  := by
            omega
        have h₃ : y % 7 = 0 ∨ y % 7 = 1 ∨ y % 7 = 2 ∨ y % 7 = 3 ∨ y % 7 = 4 ∨ y % 7 = 5 ∨ y % 7 = 6  := by
            omega
        --rcases h₂ with (h₂ | h₂ | h₂ | h₂ | h₂ | h₂ | h₂) <;>
        --rcases h₃ with (h₃ | h₃ | h₃ | h₃ | h₃ | h₃ | h₃) <;>
        --
        --(try omega) <;>
        --(try {
            --rcases h₄ with (h₄ | h₄ | h₄ | h₄ | h₄ | h₄ | h₄) <;>
            --simp [h₄, pow_three, Int.mul_emod, Int.sub_emod, Int.add_emod, Int.emod_emod] at h₁ ⊢ <;>
            --omega
        --}) <;>
        --(try omega) <;>
        --(try {
            --omega
        --}) <;>
        --(try {
            --ring_nf at h₁ ⊢
            --omega
        --})
        --<;>
    
        simp_all only [EuclideanDomain.mod_eq_zero]
  
    omega