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
theorem amc12a_2013_p4 : (2 ^ 2014 + 2 ^ 2012) / (2 ^ 2014 - 2 ^ 2012) = (5 : ℝ) / 3 := by
  have h_main : (2 ^ 2014 + 2 ^ 2012 : ℝ) / (2 ^ 2014 - 2 ^ 2012) = (5 : ℝ) / 3 := by
    have h₀ : (2 : ℝ) ^ 2014 - (2 : ℝ) ^ 2012 = (2 : ℝ) ^ 2012 * 3 := by
      have h₁ : (2 : ℝ) ^ 2014 = (2 : ℝ) ^ 2012 * 2 ^ 2 := by
        ring_nf
        <;> norm_num
        <;> ring_nf
        <;> norm_num
        <;> rfl
      rw [h₁]
      ring_nf
      <;> norm_num
      <;> ring_nf
      <;> norm_num
    have h₁ : (2 : ℝ) ^ 2014 + (2 : ℝ) ^ 2012 = (2 : ℝ) ^ 2012 * 5 := by
      have h₂ : (2 : ℝ) ^ 2014 = (2 : ℝ) ^ 2012 * 2 ^ 2 := by
        ring_nf
        <;> norm_num
        <;> ring_nf
        <;> norm_num
      rw [h₂]
      ring_nf
      <;> norm_num
      <;> ring_nf
      <;> norm_num
    rw [h₀, h₁]
    have h₂ : (2 : ℝ) ^ 2012 > 0  := by
      positivity
    field_simp [h₂]
    <;> ring_nf
    <;> field_simp [h₂]
    <;> ring_nf
    <;> norm_num
    <;> linarith
  exact h_main