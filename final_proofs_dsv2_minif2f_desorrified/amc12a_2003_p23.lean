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
theorem amc12a_2003_p23 (S : Finset ℕ)
    (h₀ : ∀ k : ℕ, k ∈ S ↔ 0 < k ∧ (k * k : ℕ) ∣ ∏ i in Finset.Icc 1 9, i !) : S.card = 672 := by
    have h_main : S.card = 672 := by
        have h₁ : S = Finset.filter (fun k => 0 < k) (Finset.filter (fun k => (k * k) ∣ ∏ i in Finset.Icc 1 9, i !) (Finset.range 10000)) := by
            apply Finset.ext
            intro k
            simp only [Finset.mem_filter, Finset.mem_range, h₀, Finset.mem_Icc, Nat.lt_succ_iff]
            <;>
            by_cases h : 0 < k <;>
            by_cases h' : (k * k) ∣ ∏ i in Finset.Icc 1 9, i ! <;>
            simp_all [Nat.lt_succ_iff] <;>
            (try omega) <;>
            (try
                {
                    norm_num at *
                    <;>
                    (try omega) <;>
                    (try
                        {
                            rcases k with (_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k) <;>
                            simp_all [Finset.prod_Icc_succ_top, Nat.factorial, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm
                                Nat.dvd_iff_mod_eq_zero, Nat.pow_succ] <;>
                            norm_num <;>
                            ring_nf at * <;>
                            omega
                        })
                }) <;>
            (try
                {
                    rcases k with (_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k) <;>
                    simp_all [Finset.prod_Icc_succ_top, Nat.factorial, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm
                        Nat.dvd_iff_mod_eq_zero, Nat.pow_succ] <;>
                    norm_num <;>
                    ring_nf at * <;>
                    omega
                })
            try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


            
            have h_main : k ≤ 9999 := by
                have h₁ : k * k ∣ sf(9 : ℕ) := by
                    gcongr
                have h₂ : k * k ∣ 285 := by
                    have h₃ : sf (9 : ℕ) = 285 := by
            
                        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


                        


                    rw [h₃] at h₁
                    exact h₁
                have h₃ : k ≤ 9999 := by
                    have h₄ : k * k ∣ 285 := by
                        gcongr
                    have h₅ : k ≤ 285 := by
                        have h₆ : k * k ∣ 285 := by
                            try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
                        have h₇ : k * k ≤ 285 := by
                            try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
                            try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


                            


                        have h₈ : k ≤ 285 := by
                            nlinarith
                        exact h₈
                    omega
                exact h₃
            exact h_main

        rw [h₁]
    
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
        

    exact h_main