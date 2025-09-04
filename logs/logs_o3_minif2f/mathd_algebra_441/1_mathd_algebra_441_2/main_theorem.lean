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

lemma mathd_algebra_441_2
  (x : ℝ)
  (h₀ : ¬x = (0 : ℝ))
  (step1_simplified step1 : x ^ (4 : ℕ) * x⁻¹ ^ (3 : ℕ) * (6 / 7 : ℝ) = x * (6 / 7 : ℝ)) :
  x * x⁻¹ * (10 : ℝ) = (10 : ℝ) := by
  have h₁ : x * x⁻¹ = 1 := by
    have h₂ : x ≠ 0 := h₀
    field_simp [h₂]
    <;>
    ring
    <;>
    simp_all [h₂]
    <;>
    norm_num
  
  have h₂ : x * x⁻¹ * (10 : ℝ) = (10 : ℝ) := by
    rw [h₁]
    <;> norm_num
    <;> linarith
  
  exact h₂
