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
theorem mathd_algebra_293 (x : NNReal) :
    Real.sqrt (60 * x) * Real.sqrt (12 * x) * Real.sqrt (63 * x) = 36 * x * Real.sqrt (35 * x) := by
  have h_main : Real.sqrt (60 * x) * Real.sqrt (12 * x) * Real.sqrt (63 * x) = 36 * x * Real.sqrt (35 * x) := by
    have h₁ : Real.sqrt (60 * x) * Real.sqrt (12 * x) * Real.sqrt (63 * x) = Real.sqrt ((60 * x) * (12 * x) * (63 * x)) := by
      have h₂ : Real.sqrt (60 * x) * Real.sqrt (12 * x) * Real.sqrt (63 * x) = Real.sqrt ((60 * x) * (12 * x) * (63 * x)) := by
        have h₃ : Real.sqrt (60 * x) * Real.sqrt (12 * x) * Real.sqrt (63 * x) = Real.sqrt ((60 * x) * (12 * x) * (63 * x)) := by
          have h₄ : Real.sqrt (60 * x) * Real.sqrt (12 * x) * Real.sqrt (63 * x) = Real.sqrt ((60 * x) * (12 * x) * (63 * x)) := by
            have h₅ : Real.sqrt (60 * x) * Real.sqrt (12 * x) * Real.sqrt (63 * x) = Real.sqrt ((60 * x) * (12 * x) * (63 * x)) := by
              rw [← Real.sqrt_mul, ← Real.sqrt_mul] <;>
                positivity
            rw [h₅]
          rw [h₄]
        rw [h₃]
      rw [h₂]
    rw [h₁]
    have h₂ : Real.sqrt ((60 * x) * (12 * x) * (63 * x)) = 36 * x * Real.sqrt (35 * x) := by
      have h₃ : (60 * x : ℝ) * (12 * x) * (63 * x) = (36 * x : ℝ) ^ 2 * (35 * x) := by
        ring_nf
        <;> field_simp [mul_assoc]
        <;> ring_nf
        <;> norm_cast
        <;> ring_nf
        <;> field_simp [mul_assoc]
        <;> ring_nf
        <;> norm_cast
      have h₄ : Real.sqrt ((60 * x) * (12 * x) * (63 * x)) = Real.sqrt ((36 * x : ℝ) ^ 2 * (35 * x)) := by
        rw [h₃]
        <;> simp [mul_assoc]
        <;> ring_nf
        <;> field_simp [mul_assoc]
        <;> ring_nf
        <;> norm_cast
      rw [h₄]
      have h₅ : Real.sqrt ((36 * x : ℝ) ^ 2 * (35 * x)) = 36 * x * Real.sqrt (35 * x) := by
        have h₆ : Real.sqrt ((36 * x : ℝ) ^ 2 * (35 * x)) = 36 * x * Real.sqrt (35 * x) := by
          have h₇ : Real.sqrt ((36 * x : ℝ) ^ 2 * (35 * x)) = 36 * x * Real.sqrt (35 * x) := by
            have h₈ : Real.sqrt ((36 * x : ℝ) ^ 2 * (35 * x)) = 36 * x * Real.sqrt (35 * x) := by
              have h₉ : Real.sqrt ((36 * x : ℝ) ^ 2 * (35 * x)) = 36 * x * Real.sqrt (35 * x) := by
                rw [Real.sqrt_eq_iff_sq_eq (by positivity) (by positivity)]
                nlinarith [Real.sqrt_nonneg (35 * x), Real.sq_sqrt (show (0 : ℝ) ≤ 35 * x by positivity)]
              rw [h₉]
            rw [h₈]
          rw [h₇]
        rw [h₆]
      rw [h₅]
    rw [h₂]
  exact h_main