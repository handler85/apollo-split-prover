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
theorem mathd_algebra_137 (x : ℕ) (h₀ : ↑x + (4 : ℝ) / (100 : ℝ) * ↑x = 598) : x = 575 := by
  have h₁ : x = 575 := by
    have h₂ : (x : ℝ) + (4 : ℝ) / (100 : ℝ) * (x : ℝ) = 598  := by
      exact_mod_cast h₀
    have h₃ : (x : ℝ) * (104 / 100 : ℝ) = 598 := by
      ring_nf at h₂ ⊢
      <;> linarith
    have h₄ : (x : ℝ) = 598 / (104 / 100 : ℝ) := by
      field_simp at h₃ ⊢
      <;> nlinarith
    have h₅ : (x : ℝ) = 575 := by
      norm_num at h₄ ⊢
      <;>
      (try norm_num) <;>
      (try linarith) <;>
      (try
        {
          field_simp at h₄ ⊢
          <;> ring_nf at h₄ ⊢ <;> nlinarith
        }) <;>
      (try
        {
          norm_num at h₄ ⊢ <;>
          nlinarith
        })
      <;>
      nlinarith
    have h₆ : x = 575 := by
      norm_cast at h₅ ⊢
      <;>
      (try norm_num at h₅ ⊢) <;>
      (try linarith) <;>
      (try
        {
          field_simp at h₅ ⊢
          <;> ring_nf at h₅ ⊢ <;> nlinarith
        }) <;>
      (try
        {
          norm_num at h₅ ⊢ <;>
          nlinarith
        })
      <;>
      nlinarith
    exact h₆
  exact h₁