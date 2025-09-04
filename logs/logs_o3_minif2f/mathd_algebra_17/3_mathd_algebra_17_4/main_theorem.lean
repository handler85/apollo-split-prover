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

lemma mathd_algebra_17_4
  (a : ℝ)
  (h9 : (1 : ℝ) + a = (9 : ℝ))
  (h8 h7 h6 h5 h₀ : True) :
  a = (8 : ℝ) := by
  have h_main : a = 8 := by
    have h : a = 8 := by
      -- Subtract 1 from both sides of the equation to solve for a
      linarith
    exact h
  exact h_main
