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

lemma mathd_algebra_342_1
  (a d : ℝ)
  (h₀ : ∑ k ∈ Finset.range (5 : ℕ), (a + (↑k : ℝ) * d) = (70 : ℝ))
  (h₁ : ∑ k ∈ Finset.range (10 : ℕ), (a + (↑k : ℝ) * d) = (210 : ℝ)) :
  (5 : ℝ) * a + (10 : ℝ) * d = (70 : ℝ) := by
  have h_sum_five : (∑ k in Finset.range 5, (a + (k : ℝ) * d)) = (5 : ℝ) * a + (10 : ℝ) * d := by
    norm_num [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    <;>
    ring_nf
    <;>
    norm_num
    <;>
    linarith
  
  have h_sum_ten : (∑ k in Finset.range 10, (a + (k : ℝ) * d)) = (10 : ℝ) * a + (45 : ℝ) * d := by
    norm_num [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    <;>
    ring_nf at * <;>
    linarith
  
  have h_main : (5 : ℝ) * a + (10 : ℝ) * d = (70 : ℝ) := by
    have h₂ := h₀
    have h₃ := h₁
    have h₄ := h_sum_five
    have h₅ := h_sum_ten
    simp [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ] at h₂ h₃ h₄ h₅
    -- Simplify the given sums to find the values of a and d
    -- Use linear arithmetic to solve for the final result
    nlinarith [sq_nonneg (a + 2 * d), sq_nonneg (a + 3 * d), sq_nonneg (a + 4 * d),
      sq_nonneg (a + 5 * d), sq_nonneg (a + 6 * d), sq_nonneg (a + 7 * d), sq_nonneg (a + 8 * d),
      sq_nonneg (a + 9 * d)]
  
  simpa using h_main
