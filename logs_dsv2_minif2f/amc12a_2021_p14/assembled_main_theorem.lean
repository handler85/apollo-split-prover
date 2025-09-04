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
theorem amc12a_2021_p14 :
    ((∑ k in Finset.Icc 1 20, Real.logb (5 ^ k) (3 ^ k ^ 2)) *
        ∑ k in Finset.Icc 1 100, Real.logb (9 ^ k) (25 ^ k)) = 21000 := by
    --have h_main : ((∑ k in Finset.Icc 1 20, Real.logb (5 ^ k) (3 ^ k ^ 2)) * ∑ k in Finset.Icc 1 100, Real.logb (9 ^ k) (25 ^ k)) = 21000 := by
        ----have h₁ : (∑ k in Finset.Icc 1 20, Real.logb (5 ^ k) (3 ^ k ^ 2)) = (Real.log 3 / Real.log 5) * 210 := by
            ------have h₁ : ∀ k : ℕ, k ∈ Finset.Icc 1 20 → Real.logb (5 ^ k) (3 ^ k ^ 2) = (k * Real.log 3) / (k * Real.log 5) := by
                ----
                ------have h₂ : k ∈ Finset.Icc 1 20  := by
                    ------
                    ------try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
                    sorry

                ------have h₃ : 1 ≤ k := by
                    ------simp [Finset.mem_Icc] at h₂
                    ------linarith
                ------have h₄ : k ≤ 20 := by
                    ------simp [Finset.mem_Icc] at h₂
                    ------linarith
                ------have h₅ : Real.logb (5 ^ k) (3 ^ k ^ 2) = Real.log (3 ^ k ^ 2) / Real.log (5 ^ k) := by
                    ------rw [Real.logb]
                    ------<;> simp [Real.log_rpow]
                    ------<;> ring_nf
                ------rw [h₅]
                ------have h₆ : Real.log (3 ^ k ^ 2) = k ^ 2 * Real.log 3 := by
                    ------rw [Real.log_pow]
                    ------<;> ring_nf
                    ------<;> field_simp
                ------have h₇ : Real.log (5 ^ k) = k * Real.log 5 := by
                    ------rw [Real.log_pow]
                    ------<;> ring_nf
                    ------<;> field_simp
                ------rw [h₆, h₇]
                ------have h₈ : (k ^ 2 * Real.log 3) / (k * Real.log 5) = (k * Real.log 3) / (k * Real.log 5) := by
                    ------have h₉ : k ≠ 0 := by
                        ------intro h
                        ------simp_all [Finset.mem_Icc]
                        ------<;> linarith
                    ------field_simp [h₉]
                    ------<;> ring_nf
                    ------
                    ------<;> ring_nf
                ------rw [h₈]
                ------<;> field_simp [h₃, h₄]
                ------<;> ring_nf
                ------<;> field_simp [h₃, h₄]
                ------<;> nlinarith
                ------
                ------
                ----
        
            try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
            sorry

    
    
    
  