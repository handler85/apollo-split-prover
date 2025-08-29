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
theorem algebra_others_exirrpowirrrat : ∃ a b : ℝ, Irrational a ∧ Irrational b ∧ ¬Irrational (a ^ b) := by
    let sqrt2 : ℝ := Real.sqrt 2
    by_cases h : Irrational (sqrt2 ^ sqrt2)
    · -- Case 1: sqrt2^sqrt2 is irrational.
        let a : ℝ := sqrt2 ^ sqrt2
        let b : ℝ := sqrt2
        have irr_a : Irrational a  := by

            exact h
        have irr_b : Irrational b := by
            exact irrational_sqrt_two
        have calc1 : a ^ b = (sqrt2 ^ sqrt2) ^ sqrt2 := by
            linarith
        have calc2 : (sqrt2 ^ sqrt2) ^ sqrt2 = sqrt2 ^ (sqrt2 * sqrt2) := by
            try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith



            have h_main : (sqrt2 ^ sqrt2) ^ sqrt2 = sqrt2 ^ (sqrt2 * sqrt2) := by
                have h₁ : 0 < sqrt2 := by
                    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
                    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith





                rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ sqrt2) sqrt2 sqrt2]
                <;> ring_nf
                <;> norm_num
                <;>
                simp_all [Real.sqrt_eq_iff_sq_eq]
                <;>
                ring_nf
                <;>
                field_simp
                <;>
                linarith
            rw [h_main]
            <;> ring_nf
            <;> simp_all [Real.sqrt_eq_iff_sq_eq]
            <;> ring_nf
            <;> field_simp
            <;> linarith

        have calc3 : sqrt2 ^ (sqrt2 * sqrt2) = sqrt2 ^ 2 := by
            try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith



            try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
            try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith






        have calc4 : sqrt2 ^ 2 = 2 := by
            try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith



            have h_main : (sqrt2 : ℝ) ^ (2 : ℕ) = (2 : ℝ) := by
                try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
                try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


                


            have h₁ : sqrt2 ^ (2 : ℕ) = (2 : ℝ) := by
                simpa [h_main] using h_main
            exact h₁

        have rat : ¬ Irrational (a ^ b) := by
            simp_all only [not_irrational_ofNat, not_false_eq_true]
        exact ⟨a, b, irr_a, irr_b, rat⟩
    · -- Case 2: sqrt2^sqrt2 is not irrational (i.e. it is rational).
        let a : ℝ := sqrt2
        let b : ℝ := sqrt2
        have irr_a : Irrational a := by
            exact irrational_sqrt_two
        have irr_b : Irrational b := by
            exact irr_a
        have rat : ¬ Irrational (a ^ b) := by
            exact h
        exact ⟨a, b, irr_a, irr_b, rat⟩
