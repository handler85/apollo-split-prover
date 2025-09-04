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

lemma mathd_algebra_80_1_1
  (x : ℝ)
  (h₀ : ¬x = (-1 : ℝ))
  (h₃ : ¬(1 : ℝ) + x = (0 : ℝ))
  (h₁ : (-9 : ℝ) + x = (2 : ℝ) + x * (2 : ℝ)) :
  x + x ^ (2 : ℕ) = (-11 : ℝ) - x * (11 : ℝ) := by
  have h_x : x = -11 := by
    have h₂ : x = -11 := by
      -- Solve for x using the equation -9 + x = 2 + 2 * x
      apply Eq.symm
      linarith
    exact h₂
  
  have h_main : x + x ^ (2 : ℕ) = (-11 : ℝ) - x * (11 : ℝ) := by
    rw [h_x]
    norm_num
    <;>
    ring_nf
    <;>
    norm_num
    <;>
    linarith
  
  rw [h_main]
  <;>
  norm_num
  <;>
  linarith
