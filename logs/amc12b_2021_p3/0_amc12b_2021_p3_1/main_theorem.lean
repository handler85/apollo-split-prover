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

lemma amc12b_2021_p3_1
  (x : ℝ)
  (h₂ : (1 : ℝ) + ((2 : ℝ) + ((3 : ℝ) + x)⁻¹ * (2 : ℝ))⁻¹ = (53 / 38 : ℝ))
  (h₀ : True) :
  ((2 : ℝ) + ((3 : ℝ) + x)⁻¹ * (2 : ℝ))⁻¹ * (38 : ℝ) = (15 : ℝ) := by
  have h_main : ((2 : ℝ) + ((3 : ℝ) + x)⁻¹ * (2 : ℝ))⁻¹ * (38 : ℝ) = (15 : ℝ) := by
    have h₃ : ((2 : ℝ) + ((3 : ℝ) + x)⁻¹ * (2 : ℝ))⁻¹ = (15 / 38 : ℝ) := by
      have h₄ : (1 : ℝ) + ((2 : ℝ) + ((3 : ℝ) + x)⁻¹ * (2 : ℝ))⁻¹ = (53 / 38 : ℝ) := h₂
      have h₅ : ((2 : ℝ) + ((3 : ℝ) + x)⁻¹ * (2 : ℝ))⁻¹ = (53 / 38 : ℝ) - 1 := by linarith
      rw [h₅]
      norm_num
      <;> linarith
    rw [h₃]
    <;> norm_num
    <;> linarith
  
  exact h_main
