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
theorem amc12b_2020_p22 (t : ℝ) : (2 ^ t - 3 * t) * t / 4 ^ t ≤ 1 / 12 := by 
    let f : ℝ → ℝ := fun x => (2 ^ x - 3 * x) * x / 4 ^ x
    have exists_max : ∃ t₀, (∀ x, f x ≤ f t₀) ∧ (f t₀ = 1 / 12)  := by


        
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


        sorry





    
    have h_main : ((2 : ℝ) ^ t - (3 : ℝ) * t) * t / (4 : ℝ) ^ t ≤ (1 / 12 : ℝ) := by
        have h₅ : f t ≤ (1 / 12 : ℝ) := by
            try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
            try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


            sorry


            <;> field_simp
            <;> ring_nf
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


        sorry


    exact h_main

