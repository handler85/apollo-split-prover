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
theorem algebra_9onxpypzleqsum2onxpy (x y z : ℝ) (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) :
    9 / (x + y + z) ≤ 2/(x+y) + 2/(y+z) + 2/(z+x) := by
  try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


  
  have h_main : (2 : ℝ) / (x + y) + (2 : ℝ) / (y + z) + (2 : ℝ) / (z + x) ≥ 9 / (x + y + z) := by
    have h₁ : 0 < x := by linarith
    have h₂ : 0 < y := by linarith
    have h₃ : 0 < z := by linarith
    have h₄ : 0 < x + y := by linarith
    have h₅ : 0 < y + z := by linarith
    have h₆ : 0 < z + x := by linarith
    have h₇ : 0 < x + y + z := by linarith
    have h₈ : 0 < x * y := by positivity
    have h₉ : 0 < y * z := by positivity
    have h₁₀ : 0 < z * x := by positivity
    field_simp
    rw [div_le_div_iff (by positivity) (by positivity)]
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      mul_nonneg h₁.le h₂.le, mul_nonneg h₂.le h₃.le, mul_nonneg h₃.le h₁.le,
      mul_nonneg (sq_nonneg (x - y)) h₃.le, mul_nonneg (sq_nonneg (y - z)) h₁.le,
      mul_nonneg (sq_nonneg (z - x)) h₂.le,
      mul_nonneg (sq_nonneg (x - y + z)) h₃.le, mul_nonneg (sq_nonneg (y - z + x)) h₁.le,
      mul_nonneg (sq_nonneg (z - x + y)) h₂.le]
  
  have h₁ : (9 : ℝ) / (x + y + z) ≤ (2 : ℝ) / (x + y) + (2 : ℝ) / (y + z) + (2 : ℝ) / (z + x) := by
    linarith
  exact h₁


