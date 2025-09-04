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

lemma amc12b_2020_p21_1
  (S : Finset ℕ)
  (h₀ : ∀ (n : ℕ), n ∈ S ↔ (0 : ℕ) < n ∧ ((↑n : ℝ) + (1000 : ℝ)) / (70 : ℝ) = (↑n.sqrt : ℝ))
  (h1 : ∀ (n : ℕ), (0 : ℕ) < n → ((↑n : ℝ) + (1000 : ℝ)) / (70 : ℝ) = (↑n.sqrt : ℝ) → n = (70 : ℕ) * n.sqrt - (1000 : ℕ)) :
  ∀ (k : ℕ), (1000 : ℕ) < k * (70 : ℕ) → (15 : ℕ) ≤ k := by
  have h_main : ∀ (k : ℕ), (1000 : ℕ) < k * (70 : ℕ) → (15 : ℕ) ≤ k := by
    intro k hk
    have h₁ : k ≥ 15 := by
      by_contra h
      -- We will show that if k < 15, then k * 70 ≤ 1000, which contradicts the given condition k * 70 > 1000.
      have h₂ : k ≤ 14 := by linarith
      interval_cases k <;> norm_num at hk ⊢ <;>
        (try omega) <;>
        (try {
          have h₃ := h1 49 (by norm_num)
          have h₄ := h3
          have h₅ := h3
          have h₆ := h3
          norm_num [Nat.sqrt_eq] at h₃ h₄ h₅ h₆ <;>
            simp_all [Nat.div_eq_of_lt] <;>
            ring_nf at * <;>
            norm_num at * <;>
            nlinarith [Real.sqrt_nonneg 49, Real.sq_sqrt (show (0 : ℝ) ≤ 49 by norm_num)]
          <;>
          linarith
        }) <;>
        (try {
          have h₃ := h1 1 (by norm_num)
          have h₄ := h3
          have h₅ := h3
          have h₆ := h3
          norm_num [Nat.sqrt_eq] at h₃ h₄ h₅ h₆ <;>
            simp_all [Nat.div_eq_of_lt] <;>
            ring_nf at * <;>
            norm_num at * <;>
            nlinarith [Real.sqrt_nonneg 1, Real.sq_sqrt (show (0 : ℝ) ≤ 1 by norm_num)]
          <;>
          linarith
        }) <;>
        (try {
          have h₃ := h1 9 (by norm_num)
          have h₄ := h3
          have h₅ := h3
          have h₆ := h3
          norm_num [Nat.sqrt_eq] at h₃ h₄ h₅ h₆ <;>
            simp_all [Nat.div_eq_of_lt] <;>
            ring_nf at * <;>
            norm_num at * <;>
            nlinarith [Real.sqrt_nonneg 9, Real.sq_sqrt (show (0 : ℝ) ≤ 9 by norm_num)]
          <;>
          linarith
        }) <;>
        (try {
          have h₃ := h1 4 (by norm_num)
          have h₄ := h3
          have h₅ := h3
          have h₆ := h3
          norm_num [Nat.sqrt_eq] at h₃ h₄ h₅ h₆ <;>
            simp_all [Nat.div_eq_of_lt] <;>
            ring_nf at * <;>
            norm_num at * <;>
            nlinarith [Real.sqrt_nonneg 4, Real.sq_sqrt (show (0 : ℝ) ≤ 4 by norm_num)]
          <;>
          linarith
        }) <;>
        (try {
          have h₃ := h1 16 (by norm_num)
          have h₄ := h3
          have h₅ := h3
          have h₆ := h3
          norm_num [Nat.sqrt_eq] at h₃ h₄ h₅ h₆ <;>
            simp_all [Nat.div_eq_of_lt] <;>
            ring_nf at * <;>
            norm_num at * <;>
            nlinarith [Real.sqrt_nonneg 16, Real.sq_sqrt (show (0 : ℝ) ≤ 16 by norm_num)]
          <;>
          linarith
        }) <;>
        (try {
          have h₃ := h1 25 (by norm_num)
          have h₄ := h3
          have h₅ := h3
          have h₆ := h3
          norm_num [Nat.sqrt_eq] at h₃ h₄ h₅ h₆ <;>
            simp_all [Nat.div_eq_of_lt] <;>
            ring_nf at * <;>
            norm_num at * <;>
            nlinarith [Real.sqrt_nonneg 25, Real.sq_sqrt (show (0 : ℝ) ≤ 25 by norm_num)]
          <;>
          linarith
        }) <;>
        (try {
          have h₃ := h1 36 (by norm_num)
          have h₄ := h3
          have h₅ := h3
          have h₆ := h3
          norm_num [Nat.sqrt_eq] at h₃ h₄ h₅ h₆ <;>
            simp_all [Nat.div_eq_of_lt] <;>
            ring_nf at * <;>
            norm_num at * <;>
            nlinarith [Real.sqrt_nonneg 36, Real.sq_sqrt (show (0 : ℝ) ≤ 36 by norm_num)]
          <;>
          linarith
        }) <;>
        (try {
          have h₃ := h1 49 (by norm_num)
          have h₄ := h3
          have h₅ := h3
          have h₆ := h3
          norm_num [Nat.sqrt_eq] at h₃ h₄ h₅ h₆ <;>
            simp_all [Nat.div_eq_of_lt] <;>
            ring_nf at * <;>
            norm_num at * <;>
            nlinarith [Real.sqrt_nonneg 49, Real.sq_sqrt (show (0 : ℝ) ≤ 49 by norm_num)]
          <;>
          linarith
        }) <;>
        (try {
          have h₃ := h1 64 (by norm_num)
          have h₄ := h3
          have h₅ := h3
          have h₆ := h3
          norm_num [Nat.sqrt_eq] at h₃ h₄ h₅ h₆ <;>
            simp_all [Nat.div_eq_of_lt] <;>
            ring_nf at * <;>
            norm_num at * <;>
            nlinarith [Real.sqrt_nonneg 64, Real.sq_sqrt (show (0 : ℝ) ≤ 64 by norm_num)]
          <;>
          linarith
        }) <;>
        (try {
          have h₃ := h1 81 (by norm_num)
          have h₄ := h3
          have h₅ := h3
          have h₆ := h3
          norm_num [Nat.sqrt_eq] at h₃ h₄ h₅ h₆ <;>
            simp_all [Nat.div_eq_of_lt] <;>
            ring_nf at * <;>
            norm_num at * <;>
            nlinarith [Real.sqrt_nonneg 81, Real.sq_sqrt (show (0 : ℝ) ≤ 81 by norm_num)]
          <;>
          linarith
        }) <;>
        (try {
          have h₃ := h1 100 (by norm_num)
          have h₄ := h3
          have h₅ := h3
          have h₆ := h3
          norm_num [Nat.sqrt_eq] at h₃ h₄ h₅ h₆ <;>
            simp_all [Nat.div_eq_of_lt] <;>
            ring_nf at * <;>
            norm_num at * <;>
            nlinarith [Real.sqrt_nonneg 100, Real.sq_sqrt (show (0 : ℝ) ≤ 100 by norm_num)]
          <;>
          linarith
        })
    exact h₁
  exact h_main
