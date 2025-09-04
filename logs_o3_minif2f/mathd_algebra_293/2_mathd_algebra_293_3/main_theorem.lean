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
lemma mathd_algebra_293_3
    (x : NNReal)
    (h3 : √(60 : ℝ) * √(12 : ℝ) * √(63 : ℝ) = √(35 : ℝ) * (36 : ℝ) ∨ x = (0 : NNReal))
    (h2 : √(↑x : ℝ) ^ (3 : ℕ) * √(60 : ℝ) * √(12 : ℝ) * √(63 : ℝ) = √(↑x : ℝ) ^ (3 : ℕ) * √(35 : ℝ) * (36 : ℝ))
    (h1 : True) :
    √(45360 : ℝ) * √(↑x : ℝ) ^ (3 : ℕ) = √(↑x : ℝ) * (↑x : ℝ) * √(35 : ℝ) * (36 : ℝ) := by
    have h4 : √(45360 : ℝ) = √(60 : ℝ) * √(12 : ℝ) * √(63 : ℝ) := by
        have h4 : √(45360 : ℝ) = √(60 : ℝ) * √(12 : ℝ) * √(63 : ℝ) := by
            have h4 : √(45360 : ℝ) = √(60 : ℝ) * √(12 : ℝ) * √(63 : ℝ) := by
                have h5 : (45360 : ℝ) = 60 * 12 * 63 := by
                    norm_num
                have h6 : √(45360 : ℝ) = √(60 : ℝ) * √(12 : ℝ) * √(63 : ℝ) := by
                    rw [h5]
                    rw [Real.sqrt_eq_iff_sq_eq (by positivity) (by positivity)]
                    simp_all only
                    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
                    sorry
                rw [h6]
                <;> ring_nf
                <;> norm_num
            rw [h4]
        rw [h4]
        <;> ring_nf
    have h5 : √(45360 : ℝ) * √(↑x : ℝ) ^ (3 : ℕ) = √(60 : ℝ) * √(12 : ℝ) * √(63 : ℝ) * √(↑x : ℝ) ^ (3 : ℕ) := by
        rw [h4]
        <;>
        simp [mul_assoc]
        <;>
        ring_nf
        <;>
        norm_num
        <;>
        field_simp
        <;>
        ring_nf
        <;>
        norm_num
    have h7 : √(45360 : ℝ) * √(↑x : ℝ) ^ (3 : ℕ) = √(35 : ℝ) * (36 : ℝ) * √(↑x : ℝ) ^ (3 : ℕ) := by
        rw [h5]
        <;> ring_nf
        <;> ring_nf
        linarith
    have h8 : √(↑x : ℝ) * (↑x : ℝ) * √(35 : ℝ) * (36 : ℝ) = √(35 : ℝ) * (36 : ℝ) * √(↑x : ℝ) ^ (3 : ℕ) := by
        have h8 : √(↑x : ℝ) * (↑x : ℝ) = √(↑x : ℝ) ^ (3 : ℕ) := by
            try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
            try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
            sorry
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
    have h9 : √(45360 : ℝ) * √(↑x : ℝ) ^ (3 : ℕ) = √(↑x : ℝ) * (↑x : ℝ) * √(35 : ℝ) * (36 : ℝ) := by
        have h9 : √(45360 : ℝ) * √(↑x : ℝ) ^ (3 : ℕ) = √(35 : ℝ) * (36 : ℝ) * √(↑x : ℝ) ^ (3 : ℕ) := by
            rw [h7]
        have h10 : √(↑x : ℝ) * (↑x : ℝ) * √(35 : ℝ) * (36 : ℝ) = √(35 : ℝ) * (36 : ℝ) * √(↑x : ℝ) ^ (3 : ℕ) := by
            rw [h8]
        linarith
    exact_mod_cast h9