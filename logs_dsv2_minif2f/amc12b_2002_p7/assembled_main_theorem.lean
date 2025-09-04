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
theorem amc12b_2002_p7 (a b c : ℕ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : b = a + 1) (h₂ : c = b + 1)
    (h₃ : a * b * c = 8 * (a + b + c)) : a ^ 2 + (b ^ 2 + c ^ 2) = 77 := by
    have h_main : a = 4 := by
        have h₄ : a * b * c = 8 * (a + b + c)  := by
      
            gcongr
        rw [h₁, h₂] at h₄
        ring_nf at h₄
        rcases a with (_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | a) <;> simp_all [mul_assoc, mul_comm, mul_left_comm]
        <;> ring_nf at h₄ ⊢ <;>
        (try omega) <;>
        (try
            {
                nlinarith
            }) <;>
        (try
            {
                ring_nf at h₄ ⊢
                nlinarith
            }) <;>
        (try
            {
                omega
            })
        <;>
        (try
            {
                nlinarith
            })
        <;>
        (try
            {
                ring_nf at h₄ ⊢
                nlinarith
            })
        <;>
        (try
            {
                omega
            })
    have h_final : a ^ 2 + (b ^ 2 + c ^ 2) = 77 := by
        subst_vars
        <;> norm_num
        <;> ring_nf at h₃ ⊢
        <;> nlinarith
    exact h_final