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

lemma mathd_algebra_293_2
  (x : NNReal)
  (h1 : True) :
  √(720 : ℝ) * √(↑x : ℝ) ^ (3 : ℕ) * √(63 : ℝ) = √(↑x : ℝ) ^ (3 : ℕ) * √(45360 : ℝ) := by
  have h_main : √(720 : ℝ) * √(↑x : ℝ) ^ (3 : ℕ) * √(63 : ℝ) = √(↑x : ℝ) ^ (3 : ℕ) * √(45360 : ℝ) := by
    have h2 : √(720 : ℝ) * √(63 : ℝ) = √(45360 : ℝ) := by
      have h3 : √(720 : ℝ) * √(63 : ℝ) = √(720 * (63 : ℝ)) := by
        rw [← Real.sqrt_mul] <;> positivity
      rw [h3]
      have h4 : √(720 * (63 : ℝ)) = √(45360 : ℝ) := by
        norm_num [Real.sqrt_eq_iff_sq_eq]
        <;> ring_nf
        <;> norm_num
        <;> rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> nlinarith [Real.sqrt_nonneg 45360, Real.sq_sqrt (show (0 : ℝ) ≤ 45360 by norm_num)]
      rw [h4]
      <;> norm_num
    calc
      √(720 : ℝ) * √(↑x : ℝ) ^ (3 : ℕ) * √(63 : ℝ) = (√(720 : ℝ) * √(63 : ℝ)) * √(↑x : ℝ) ^ (3 : ℕ) := by ring
      _ = √(45360 : ℝ) * √(↑x : ℝ) ^ (3 : ℕ) := by rw [h2]
      _ = √(↑x : ℝ) ^ (3 : ℕ) * √(45360 : ℝ) := by ring
  exact h_main
