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

lemma amc12b_2020_p13_3
  (h_main :
  Real.log (6 : ℝ) / Real.log (2 : ℝ) + Real.log (6 : ℝ) / Real.log (3 : ℝ) =
    Real.log (3 : ℝ) / Real.log (2 : ℝ) + Real.log (2 : ℝ) / Real.log (3 : ℝ) + (2 : ℝ)) :
  (0 : ℝ) < Real.log (2 : ℝ) := by
  have h₁ : (1 : ℝ) < 2 := by
    norm_num
    <;>
    linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
    <;>
    norm_num
    <;>
    linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  
  have h₂ : (0 : ℝ) < Real.log 2 := by
    have h₃ : Real.log 1 < Real.log 2 := Real.log_lt_log (by norm_num) h₁
    have h₄ : Real.log 1 = 0 := by
      simp
    have h₅ : (0 : ℝ) < Real.log 2 := by linarith
    exact h₅
  
  exact h₂
