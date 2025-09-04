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

lemma amc12b_2020_p13_2
  (h₁ : Real.log (6 : ℝ) = Real.log (2 : ℝ) + Real.log (3 : ℝ))
  (h₃ : (0 : ℝ) < Real.log (2 : ℝ)) :
  (0 : ℝ) < Real.log (3 : ℝ) := by
  have h₄ : (3 : ℝ) > 1 := by
    norm_num
    <;>
    linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  
  have h₅ : (0 : ℝ) < Real.log (3 : ℝ) := by
    have h₅₁ : Real.log (3 : ℝ) > Real.log (1 : ℝ) := by
      apply Real.log_lt_log
      · norm_num
      · linarith
    have h₅₂ : Real.log (1 : ℝ) = (0 : ℝ) := by
      simp
    linarith
  
  exact h₅
