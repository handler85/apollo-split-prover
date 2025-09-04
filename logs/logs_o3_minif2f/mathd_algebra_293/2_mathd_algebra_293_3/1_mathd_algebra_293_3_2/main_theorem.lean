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

lemma mathd_algebra_293_3_2
  (x : NNReal)
  (h3 : √(60 : ℝ) * √(12 : ℝ) * √(63 : ℝ) = √(35 : ℝ) * (36 : ℝ) ∨ x = (0 : NNReal))
  (h2 : √(↑x : ℝ) ^ (3 : ℕ) * √(60 : ℝ) * √(12 : ℝ) * √(63 : ℝ) = √(↑x : ℝ) ^ (3 : ℕ) * √(35 : ℝ) * (36 : ℝ))
  (h4 : √(45360 : ℝ) = √(60 : ℝ) * √(12 : ℝ) * √(63 : ℝ)) :
  √(↑x : ℝ) * (↑x : ℝ) = √(↑x : ℝ) ^ (3 : ℕ) := by
  have h_main : √(↑x : ℝ) * (↑x : ℝ) = √(↑x : ℝ) ^ (3 : ℕ) := by
    have h5 : √(↑x : ℝ) * (↑x : ℝ) = √(↑x : ℝ) ^ (3 : ℕ) := by
      -- Consider the cases where x = 0 or x > 0
      have h6 : √(↑x : ℝ) * (↑x : ℝ) = √(↑x : ℝ) ^ (3 : ℕ) := by
        -- Use the fact that √x ^ 3 = x * √x
        have h7 : √(↑x : ℝ) ^ (3 : ℕ) = √(↑x : ℝ) ^ 2 * √(↑x : ℝ) := by
          ring_nf
          <;>
          simp [pow_succ, pow_two]
          <;>
          ring_nf
        rw [h7]
        -- Simplify using the property of square roots
        have h8 : √(↑x : ℝ) ^ 2 = (↑x : ℝ) := by
          rw [Real.sq_sqrt (show (0 : ℝ) ≤ (↑x : ℝ) by exact by exact NNReal.coe_nonneg x)]
        rw [h8]
        <;>
        ring_nf
        <;>
        nlinarith [Real.sqrt_nonneg (↑x : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (↑x : ℝ) by exact by exact NNReal.coe_nonneg x)]
      exact h6
    exact h5
  exact h_main
