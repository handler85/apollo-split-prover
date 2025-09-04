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

lemma mathd_algebra_208_1_1:
  rexp (Real.log (1000000 : ℝ) * (1 / 3 : ℝ)) = (100 : ℝ) := by
  have h_main : rexp (Real.log (1000000 : ℝ) * (1 / 3 : ℝ)) = (100 : ℝ) := by
    have h₁ : Real.log (1000000 : ℝ) = 6 * Real.log 10 := by
      have h₂ : Real.log (1000000 : ℝ) = Real.log (10 ^ 6 : ℝ) := by norm_num
      rw [h₂]
      have h₃ : Real.log ((10 : ℝ) ^ 6) = 6 * Real.log 10 := by
        rw [Real.log_pow] <;> ring_nf <;> norm_num
        <;> linarith [Real.log_pos (by norm_num : (1 : ℝ) < 10)]
      rw [h₃]
      <;> norm_num
      <;> ring_nf
      <;> norm_num
      <;> linarith [Real.log_pos (by norm_num : (1 : ℝ) < 10)]
    rw [h₁]
    have h₂ : rexp ((6 * Real.log 10 : ℝ) * (1 / 3 : ℝ)) = 100 := by
      have h₃ : rexp ((6 * Real.log 10 : ℝ) * (1 / 3 : ℝ)) = rexp (2 * Real.log 10) := by
        ring_nf
        <;>
        norm_num
        <;>
        field_simp
        <;>
        ring_nf
      rw [h₃]
      have h₄ : rexp (2 * Real.log 10) = 100 := by
        have h₅ : rexp (2 * Real.log 10) = (10 : ℝ) ^ (2 : ℝ) := by
          rw [show (2 : ℝ) * Real.log 10 = Real.log (10 ^ 2) by
            rw [Real.log_pow] <;> norm_num
            <;> linarith [Real.log_pos (by norm_num : (1 : ℝ) < 10)]]
          rw [Real.exp_log] <;>
            norm_num
          <;>
          positivity
        rw [h₅]
        norm_num
        <;>
        ring_nf
        <;>
        norm_num
        <;>
        linarith [Real.log_pos (by norm_num : (1 : ℝ) < 10)]
      rw [h₄]
      <;>
      norm_num
    simp_all
    <;>
    ring_nf
    <;>
    norm_num
    <;>
    linarith [Real.log_pos (by norm_num : (1 : ℝ) < 10)]
  
  exact h_main
