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

lemma mathd_algebra_441_1
  (x : ℝ)
  (h₀ : ¬x = (0 : ℝ))
  (step1 : True) :
  x ^ (4 : ℕ) * x⁻¹ ^ (3 : ℕ) * (6 / 7 : ℝ) = x * (6 / 7 : ℝ) := by
  have h_main : x ^ (4 : ℕ) * x⁻¹ ^ (3 : ℕ) * (6 / 7 : ℝ) = x * (6 / 7 : ℝ) := by
    have h₁ : x ≠ 0 := by exact h₀
    -- Simplify the expression using properties of exponents and division
    field_simp [h₁, pow_succ, mul_assoc, mul_comm, mul_left_comm]
    <;> ring_nf
    <;> simp_all [mul_assoc]
    <;> field_simp [h₁]
    <;> ring_nf
    <;> norm_cast
    <;> simp_all [pow_succ]
    <;> ring_nf
    <;> field_simp [h₁]
    <;> norm_num
    <;> ring_nf
    <;> norm_cast
    <;> simp_all [pow_succ]
    <;> ring_nf
    <;> field_simp [h₁]
    <;> norm_num
  exact h_main
