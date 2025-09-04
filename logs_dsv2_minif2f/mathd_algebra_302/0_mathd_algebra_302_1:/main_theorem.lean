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

lemma mathd_algebra_302_1:
  Complex.I ^ (2 : ℕ) * (1 / 4 : ℂ) = (-1 / 4 : ℂ) := by
  have h_main : Complex.I ^ (2 : ℕ) * (1 / 4 : ℂ) = (-1 / 4 : ℂ) := by
    have h : Complex.I ^ 2 = -1 := by
      rw [show Complex.I ^ 2 = -1 by
        simp [Complex.ext_iff, pow_two, Complex.I_mul_I]
        <;> norm_num]
    rw [h]
    <;> ring_nf
    <;> norm_num
    <;> field_simp [Complex.ext_iff, pow_two, Complex.I_mul_I]
    <;> norm_num
    <;> simp_all [Complex.ext_iff, pow_two, Complex.I_mul_I]
    <;> norm_num
    <;> linarith
  
  exact h_main
