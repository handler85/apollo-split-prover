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

lemma amc12a_2021_p18_4
  (f : ℚ → ℝ)
  (h₀ : ∀ (x : ℚ), (0 : ℚ) < x → ∀ (y : ℚ), (0 : ℚ) < y → f (x * y) = f x + f y)
  (h₁ : ∀ (p : ℕ), Nat.Prime p → f (↑p : ℚ) = (↑p : ℝ))
  (f_one : f (1 : ℚ) = (0 : ℝ))
  (f_inv : ∀ (x : ℚ), (0 : ℚ) < x → f x⁻¹ = -f x)
  (f_pow : ∀ (p n : ℕ), Nat.Prime p → f ((↑p : ℚ) ^ n) = (↑n : ℝ) * (↑p : ℝ)) :
  f (25 : ℚ) = (10 : ℝ) := by
  have h_main : f (25 : ℚ) = (10 : ℝ) := by
    have h₂ : f ((5 : ℚ) ^ 2) = (2 : ℝ) * (5 : ℝ) := by
      have h₂₁ : f ((5 : ℚ) ^ 2) = (2 : ℝ) * (5 : ℝ) := by
        have h₂₂ : f ((5 : ℚ) ^ 2) = f ((↑(5 : ℕ) : ℚ) ^ (2 : ℕ)) := by norm_cast
        rw [h₂₂]
        have h₂₃ : f ((↑(5 : ℕ) : ℚ) ^ (2 : ℕ)) = ( (2 : ℝ) : ℝ) * ( (5 : ℝ) : ℝ) := by
          have h₂₄ := f_pow 5 2 (by decide)
          norm_num at h₂₄ ⊢
          <;> linarith
        simpa using h₂₃
      exact h₂₁
    norm_num [pow_two] at h₂ ⊢
    <;>
    (try simp_all [mul_comm]) <;>
    (try norm_num at * <;> linarith) <;>
    (try linarith [h₁ 5 (by decide)]) <;>
    (try
      {
        have h₃ := h₀ 5 (by norm_num) 5 (by norm_num)
        norm_num [mul_comm] at h₃
        <;> linarith
      }) <;>
    (try
      {
        have h₃ := h₀ 5 (by norm_num) (1/5) (by norm_num)
        norm_num [mul_comm] at h₃
        <;> linarith
      })
    <;>
    (try
      {
        have h₃ := h₀ 2 (by norm_num) 5 (by norm_num)
        norm_num [mul_comm] at h₃
        <;> linarith
      })
    <;>
    (try
      {
        have h₃ := h₀ 2 (by norm_num) (25) (by norm_num)
        norm_num [mul_comm] at h₃
        <;> linarith
      })
    <;>
    (try
      {
        have h₃ := h₀ 5 (by norm_num) (1/5) (by norm_num)
        norm_num [mul_comm] at h₃
        <;> linarith
      })
    <;>
    (try
      {
        have h₃ := h₀ 2 (by norm_num) (1/2) (by norm_num)
        norm_num [mul_comm] at h₃
        <;> linarith
      })
    <;>
    (try
      {
        have h₃ := h₀ 3 (by norm_num) 3 (by norm_num)
        norm_num [mul_comm] at h₃
        <;> linarith
      })
    <;>
    (try
      {
        have h₃ := h₀ 3 (by norm_num) (1/3) (by norm_num)
        norm_num [mul_comm] at h₃
        <;> linarith
      })
    <;>
    (try
      {
        have h₃ := h₀ 5 (by norm_num) 5 (by norm_num)
        norm_num [mul_comm] at h₃
        <;> linarith
      })
    <;>
    (try
      {
        have h₃ := h₀ 2 (by norm_num) 5 (by norm_num)
        norm_num [mul_comm] at h₃
        <;> linarith
      })
    <;>
    (try
      {
        have h₃ := h₀ 5 (by norm_num) 2 (by norm_num)
        norm_num [mul_comm] at h₃
        <;> linarith
      })
    <;>
    (try
      {
        have h₃ := h₀ 3 (by norm_num) 5 (by norm_num)
        norm_num [mul_comm] at h₃
        <;> linarith
      })
    <;>
    (try
      {
        have h₃ := h₀ 5 (by norm_num) 3 (by norm_num)
        norm_num [mul_comm] at h₃
        <;> linarith
      })
  exact h_main
