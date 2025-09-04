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

lemma mathd_algebra_293_3_1
  (x : NNReal)
  (h3 : √(60 : ℝ) * √(12 : ℝ) * √(63 : ℝ) = √(35 : ℝ) * (36 : ℝ) ∨ x = (0 : NNReal))
  (h5 : True)
  (h2 : √(60 : ℝ) * √(12 : ℝ) * √(63 : ℝ) * √(↑x : ℝ) ^ (3 : ℕ) = √(↑x : ℝ) ^ (3 : ℕ) * √(35 : ℝ) * (36 : ℝ)) :
  √(60 : ℝ) ^ (2 : ℕ) * √(12 : ℝ) ^ (2 : ℕ) * √(63 : ℝ) ^ (2 : ℕ) = (45360 : ℝ) := by
  have h_main : √(60 : ℝ) ^ (2 : ℕ) * √(12 : ℝ) ^ (2 : ℕ) * √(63 : ℝ) ^ (2 : ℕ) = (45360 : ℝ) := by
    have h4 : √(60 : ℝ) ^ (2 : ℕ) * √(12 : ℝ) ^ (2 : ℕ) * √(63 : ℝ) ^ (2 : ℕ) = (60 : ℝ) * (12 : ℝ) * (63 : ℝ) := by
      have h5 : √(60 : ℝ) ^ (2 : ℕ) = (60 : ℝ) := by
        have h6 : √(60 : ℝ) ^ (2 : ℕ) = 60 := by
          rw [show (√(60 : ℝ) ^ (2 : ℕ)) = (√(60 : ℝ) ^ 2) by norm_num]
          rw [Real.sq_sqrt (by positivity)]
          <;> norm_num
        linarith
      have h6 : √(12 : ℝ) ^ (2 : ℕ) = (12 : ℝ) := by
        have h7 : √(12 : ℝ) ^ (2 : ℕ) = 12 := by
          rw [show (√(12 : ℝ) ^ (2 : ℕ)) = (√(12 : ℝ) ^ 2) by norm_num]
          rw [Real.sq_sqrt (by positivity)]
          <;> norm_num
        linarith
      have h7 : √(63 : ℝ) ^ (2 : ℕ) = (63 : ℝ) := by
        have h8 : √(63 : ℝ) ^ (2 : ℕ) = 63 := by
          rw [show (√(63 : ℝ) ^ (2 : ℕ)) = (√(63 : ℝ) ^ 2) by norm_num]
          rw [Real.sq_sqrt (by positivity)]
          <;> norm_num
        linarith
      calc
        √(60 : ℝ) ^ (2 : ℕ) * √(12 : ℝ) ^ (2 : ℕ) * √(63 : ℝ) ^ (2 : ℕ) = (60 : ℝ) * (12 : ℝ) * (63 : ℝ) := by
          rw [h5, h6, h7]
          <;> ring
        _ = (60 : ℝ) * (12 : ℝ) * (63 : ℝ) := by rfl
    have h8 : (60 : ℝ) * (12 : ℝ) * (63 : ℝ) = (45360 : ℝ) := by
      norm_num
    linarith
  
  simpa using h_main
