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
theorem algebra_absapbon1pabsapbleqsumabsaon1pabsa (a b : ℝ) :
    abs (a + b) / (1 + abs (a + b)) ≤ abs a / (1 + abs a) + abs b / (1 + abs b) := by
  try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


  
  have h_triangle : |a + b| ≤ |a| + |b| := by
    exact?
  
  have h_main : |a + b| / ((1 : ℝ) + |a + b|) ≤ (|a| + |b|) / ((1 : ℝ) + |a| + |b|) := by
    have h₀ : 0 ≤ |a| := abs_nonneg a
    have h₁ : 0 ≤ |b| := abs_nonneg b
    have h₂ : 0 ≤ |a + b| := abs_nonneg (a + b)
    have h₃ : 0 ≤ |a| + |b| := by linarith
    have h₄ : 0 ≤ 1 + |a + b| := by positivity
    have h₅ : 0 ≤ 1 + |a| + |b| := by linarith
    have h₆ : 0 ≤ |a| * |b| := by positivity
    have h₇ : |a + b| / (1 + |a + b|) ≤ (|a| + |b|) / (1 + |a| + |b|) := by
      -- Use the fact that |a + b| ≤ |a| + |b| to compare the fractions
      rw [div_le_div_iff] <;>
        (try positivity) <;>
        (try nlinarith [abs_add a b, abs_sub a b, abs_mul a b]) <;>
        nlinarith [h_triangle, abs_add a b, abs_sub a b, abs_mul a b,
          mul_nonneg h₀ h₁, mul_nonneg h₀ (abs_nonneg b), mul_nonneg h₁ (abs_nonneg a)]
    exact h₇
  
  have h_final : (|a| + |b|) / ((1 : ℝ) + |a| + |b|) ≤ |a| / ((1 : ℝ) + |a|) + |b| / ((1 : ℝ) + |b|) := by
    have h₁ : 0 ≤ |a| := abs_nonneg a
    have h₂ : 0 ≤ |b| := abs_nonneg b
    have h₃ : 0 ≤ |a| * |b| := by positivity
    have h₄ : 0 < (1 : ℝ) + |a| + |b| := by linarith
    have h₅ : 0 < (1 : ℝ) + |a| := by linarith
    have h₆ : 0 < (1 : ℝ) + |b| := by linarith
    field_simp
    rw [div_le_div_iff (by positivity) (by positivity)]
    nlinarith [sq_nonneg (|a| - |b|), sq_nonneg (|a| - (1 : ℝ)), sq_nonneg (|b| - (1 : ℝ)),
      mul_nonneg h₁ h₂, mul_nonneg h₁ (sub_nonneg.mpr h₁), mul_nonneg h₂ (sub_nonneg.mpr h₂),
      mul_nonneg (sq_nonneg (|a| - 1)) (sq_nonneg (|b| - 1)), mul_nonneg (sq_nonneg (|a| - |b|)) (sub_nonneg.mpr h₁),
      mul_nonneg (sq_nonneg (|b| - |a|)) (sub_nonneg.mpr h₂)]
  
  have h_final_goal : |a + b| / ((1 : ℝ) + |a + b|) ≤ |a| / ((1 : ℝ) + |a|) + |b| / ((1 : ℝ) + |b|) := by
    linarith
  
  linarith


