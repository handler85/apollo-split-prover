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

lemma amc12a_2021_p18_5
  (f : ℚ → ℝ)
  (h₀ : ∀ (x : ℚ), (0 : ℚ) < x → ∀ (y : ℚ), (0 : ℚ) < y → f (x * y) = f x + f y)
  (h₁ : ∀ (p : ℕ), Nat.Prime p → f (↑p : ℚ) = (↑p : ℝ))
  (f_one : f (1 : ℚ) = (0 : ℝ))
  (f_inv : ∀ (x : ℚ), (0 : ℚ) < x → f x⁻¹ = -f x)
  (f_pow : ∀ (p n : ℕ), Nat.Prime p → f ((↑p : ℚ) ^ n) = (↑n : ℝ) * (↑p : ℝ))
  (f_25 : f (25 : ℚ) = (10 : ℝ)) :
  f (11 : ℚ) = (11 : ℝ) := by
  have h_main : f (11 : ℚ) = (11 : ℝ) := by
    have h₂ := f_pow 11 1 (by norm_num [Nat.Prime])
    norm_num at h₂ ⊢
    <;>
    (try norm_num) <;>
    (try linarith) <;>
    (try simp_all [mul_comm]) <;>
    (try ring_nf at * <;> nlinarith)
    <;>
    (try nlinarith) <;>
    (try linarith) <;>
    (try
      {
        have h₃ := f_pow 5 2 (by norm_num [Nat.Prime])
        have h₄ := f_pow 5 1 (by norm_num [Nat.Prime])
        norm_num at h₃ h₄ ⊢
        <;> nlinarith [h₀ 5 (by norm_num) 11 (by norm_num)]
      })
    <;>
    (try
      {
        have h₃ := f_pow 2 5 (by norm_num [Nat.Prime])
        have h₄ := f_pow 2 4 (by norm_num [Nat.Prime])
        have h₅ := f_pow 2 3 (by norm_num [Nat.Prime])
        have h₆ := f_pow 2 2 (by norm_num [Nat.Prime])
        have h₇ := f_pow 2 1 (by norm_num [Nat.Prime])
        norm_num at h₃ h₄ h₅ h₆ h₇ ⊢
        <;> nlinarith [h₀ 2 (by norm_num) 11 (by norm_num)]
      })
    <;>
    (try
      {
        have h₃ := f_pow 3 2 (by norm_num [Nat.Prime])
        have h₄ := f_pow 3 1 (by norm_num [Nat.Prime])
        norm_num at h₃ h₄ ⊢
        <;> nlinarith [h₀ 3 (by norm_num) 11 (by norm_num)]
      })
    <;>
    (try
      {
        have h₃ := f_pow 5 2 (by norm_num [Nat.Prime])
        have h₄ := f_pow 5 1 (by norm_num [Nat.Prime])
        norm_num at h₃ h₄ ⊢
        <;> nlinarith [h₀ 5 (by norm_num) 11 (by norm_num)]
      })
    <;>
    (try
      {
        have h₃ := f_pow 7 1 (by norm_num [Nat.Prime])
        have h₄ := f_pow 7 2 (by norm_num [Nat.Prime])
        norm_num at h₃ h₄ ⊢
        <;> nlinarith [h₀ 7 (by norm_num) 11 (by norm_num)]
      })
    <;>
    (try
      {
        have h₃ := f_pow 11 1 (by norm_num [Nat.Prime])
        norm_num at h₃ ⊢
        <;> nlinarith
      })
  exact h_main
