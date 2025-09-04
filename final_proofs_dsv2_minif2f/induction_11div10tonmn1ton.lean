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
theorem induction_11div10tonmn1ton (n : ℕ) : 11 ∣ 10 ^ n - (-1 : ℤ) ^ n := by
    have h_main : (10 : ℤ) ^ n - (-1 : ℤ) ^ n ≡ 0 [ZMOD 11] := by
        have h : ∀ n : ℕ, (10 : ℤ) ^ n - (-1 : ℤ) ^ n ≡ 0 [ZMOD 11] := by
            intro n
            rw [Int.ModEq]
            induction n using Nat.strong_induction_on with
                | h n ih =>
                    match n with
                        | 0 =>
                            norm_num [Int.emod_eq_emod_iff_emod_sub_eq_zero]
                        | 1 =>
                            norm_num [Int.emod_eq_emod_iff_emod_sub_eq_zero]
                        | 2 =>
                            norm_num [Int.emod_eq_emod_iff_emod_sub_eq_zero]
                        | n + 3 =>
              
              
              
              
              
              
                            try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


                            
                            try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
                            try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


                            sorry



        exact h n
    have h_final : 11 ∣ 10 ^ n - (-1 : ℤ) ^ n := by
        have h₁ : (10 : ℤ) ^ n - (-1 : ℤ) ^ n ≡ 0 [ZMOD 11]  := by
      
            gcongr
        have h₂ : (11 : ℤ) ∣ (10 : ℤ) ^ n - (-1 : ℤ) ^ n := by
            rw [Int.modEq_zero_iff_dvd] at h₁
            exact h₁
        exact_mod_cast h₂
    exact h_final