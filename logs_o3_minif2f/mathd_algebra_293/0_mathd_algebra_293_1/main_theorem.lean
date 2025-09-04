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

lemma mathd_algebra_293_1
  (x : NNReal) :
  √(60 : ℝ) * √(↑x : ℝ) * (√(12 : ℝ) * √(↑x : ℝ)) = √(720 : ℝ) * √(↑x : ℝ) * √(↑x : ℝ) := by
  have h_main : √(60 : ℝ) * √(↑x : ℝ) * (√(12 : ℝ) * √(↑x : ℝ)) = √(720 : ℝ) * √(↑x : ℝ) * √(↑x : ℝ) := by
    have h₀ : √(60 : ℝ) * √(↑x : ℝ) * (√(12 : ℝ) * √(↑x : ℝ)) = √(60 : ℝ) * √(12 : ℝ) * (√(↑x : ℝ) * √(↑x : ℝ)) := by
      ring_nf
      <;>
      field_simp <;>
      ring_nf <;>
      norm_num <;>
      nlinarith [Real.sqrt_nonneg (60 : ℝ), Real.sqrt_nonneg (12 : ℝ), Real.sqrt_nonneg (↑x : ℝ)]
    rw [h₀]
    have h₁ : √(60 : ℝ) * √(12 : ℝ) = √(60 * 12 : ℝ) := by
      rw [← Real.sqrt_mul (by positivity)]
      <;> ring_nf
    rw [h₁]
    have h₂ : √(60 * 12 : ℝ) = √(720 : ℝ) := by
      norm_num
      <;>
      rw [Real.sqrt_eq_iff_sq_eq] <;>
      norm_num <;>
      ring_nf <;>
      norm_num
      <;>
      nlinarith [Real.sqrt_nonneg (720 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 720 by norm_num)]
    rw [h₂]
    <;> ring_nf
    <;> field_simp [Real.sqrt_eq_iff_sq_eq] <;> ring_nf <;> norm_num <;>
    nlinarith [Real.sqrt_nonneg (720 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 720 by norm_num),
      Real.sqrt_nonneg (↑x : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (↑x : ℝ) by exact_mod_cast x.prop)]
  exact h_main
