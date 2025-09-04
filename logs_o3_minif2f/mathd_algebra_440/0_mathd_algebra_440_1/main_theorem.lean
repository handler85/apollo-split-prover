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

lemma mathd_algebra_440_1
  (x : ℝ)
  (h1 : (3 / 2 : Float) = 1.5)
  (h3 : x * (1 / 10 : ℝ) = (1 / 2 : ℝ))
  (h₀ : True) :
  x = (5 : ℝ) := by
  have h_main : x = (5 : ℝ) := by
    have h4 : x * (1 / 10 : ℝ) = (1 / 2 : ℝ) := h3
    -- Multiply both sides by 10 to eliminate the fraction
    field_simp at h4 ⊢
    <;> ring_nf at h4 ⊢ <;> nlinarith
  
  exact h_main
