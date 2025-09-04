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
theorem mathd_algebra_153 (n : ℝ) (h₀ : n = 1 / 3) :
    Int.floor (10 * n) + Int.floor (100 * n) + Int.floor (1000 * n) + Int.floor (10000 * n) = 3702 := by
  have h₁ : Int.floor (10 * n) = 3 := by
    rw [h₀]
    have h₁ : Int.floor ((10 : ℝ) * (1 / 3 : ℝ)) = 3 := by
      apply Int.floor_eq_iff.mpr
      norm_num
      <;>
      norm_num <;>
      norm_num <;>
      linarith
    simpa using h₁
  have h₂ : Int.floor (100 * n) = 33 := by
    rw [h₀]
    have h₂ : Int.floor ((100 : ℝ) * (1 / 3 : ℝ)) = 33 := by
      apply Int.floor_eq_iff.mpr
      norm_num
      <;>
      norm_num <;>
      norm_num <;>
      linarith
    simpa using h₂
  have h₃ : Int.floor (1000 * n) = 333 := by
    rw [h₀]
    have h₃ : Int.floor ((1000 : ℝ) * (1 / 3 : ℝ)) = 333 := by
      apply Int.floor_eq_iff.mpr
      norm_num
      <;>
      norm_num <;>
      norm_num <;>
      linarith
    simpa using h₃
  have h₄ : Int.floor (10000 * n) = 3333 := by
    rw [h₀]
    have h₄ : Int.floor ((10000 : ℝ) * (1 / 3 : ℝ)) = 3333 := by
      apply Int.floor_eq_iff.mpr
      norm_num
      <;>
      norm_num <;>
      norm_num <;>
      linarith
    simpa using h₄
  have h₅ : Int.floor (10 * n) + Int.floor (100 * n) + Int.floor (1000 * n) + Int.floor (10000 * n) = 3702 := by
    rw [h₁, h₂, h₃, h₄]
    <;> norm_num
    <;> rfl
  exact h₅