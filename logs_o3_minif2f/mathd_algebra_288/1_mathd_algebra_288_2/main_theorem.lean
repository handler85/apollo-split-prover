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

lemma mathd_algebra_288_2
  (x y : ℝ)
  (n : NNReal)
  (h₀ : x < (0 : ℝ))
  (hy : y = (-6 : ℝ))
  (h2_subst : √((145 : ℝ) - x * (16 : ℝ) + x ^ (2 : ℕ)) = (15 : ℝ))
  (h₃ : √((36 : ℝ) + x ^ (2 : ℕ)) = √(↑n : ℝ)) :
  √((145 : ℝ) - x * (16 : ℝ) + x ^ (2 : ℕ)) = (15 : ℝ) := by
  have h_main : √((145 : ℝ) - x * (16 : ℝ) + x ^ (2 : ℕ)) = (15 : ℝ) := by
    simpa using h2_subst
  
  exact h_main
