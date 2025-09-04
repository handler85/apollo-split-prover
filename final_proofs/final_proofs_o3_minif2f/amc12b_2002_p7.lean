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
theorem amc12b_2002_p7 (a b c : ℕ)
    (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
    (h₁ : b = a + 1)
    (h₂ : c = b + 1)
    (h₃ : a * b * c = 8 * (a + b + c)) : a^2 + b^2 + c^2 = 77 := by 
    have h_bc : c = a + 2  := by
        rw [h₂, h₁]
    have prod_eq : a * (a+1) * (a+2) = 8 * (a + (a+1) + (a+2))  := by
        rw [h₁, h_bc] at h₃
        exact h₃
    have sum_simp : a + (a+1) + (a+2) = 3*a + 3  := by
        linarith
    have eq_simplified : a * (a+1) * (a+2) = 24 * (a+1)  := by
        ring
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


        
        gcongr

    have cancel_factor : a * (a+2) = 24  := by
        linarith
    have a_eq_4 : a = 4  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


        
        have h_a_eq_4 : a = 4 := by
          rcases a with (_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | a) <;> simp_all [Nat.mul_add, Nat.add_mul, Nat.pow_succ, Nat.pow_zero]
          <;> ring_nf at *
          <;> norm_num at *
          <;> nlinarith
        rw [h_a_eq_4]
        <;> simp_all
        <;> norm_num
        <;> nlinarith


    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith