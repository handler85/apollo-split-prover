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
theorem amc12b_2020_p21 (S : Finset ℕ)
  (h₀ : ∀ n : ℕ, n ∈ S ↔ 0 < n ∧ (↑n + (1000 : ℝ)) / 70 = Int.floor (Real.sqrt n)) : S.card = 6 := by
  have h1 : ∀ n ∈ S, ∃ k : ℕ, n = 70 * k - 1000 ∧ Int.floor (Real.sqrt n) = k := by
    omega
  have h2 : ∀ k : ℕ, (70 * k - 1000 > 0) → k ≥ 15 := by
    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith



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


  have h3 : ∀ k n : ℕ, n = 70 * k - 1000 → (k^2 ≤ 70 * k - 1000 ∧ 70 * k - 1000 < (k + 1)^2) := by
    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith



    have h_false : False := by

        exact fun (k : ℕ) => False.elim h_false
    have h_main : ∀ (k : ℕ), k ^ (2 : ℕ) ≤ k * (70 : ℕ) - (1000 : ℕ) ∧ k * (70 : ℕ) - (1000 : ℕ) < (1 : ℕ) + k * (2 : ℕ) + k ^ (2 : ℕ) := by

        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith

  have h4 : ∀ k : ℕ, k^2 ≤ 70 * k - 1000 → 20 ≤ k ∧ k ≤ 50 := by
    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith



    have h_false : False := by
      have h4 := h3 80
      have h5 := h3 1000
      have h6 := h3 0
      have h7 := h3 1
      have h8 := h3 70
      have h9 := h3 81
      have h10 := h3 20
      have h11 := h3 50
      have h12 := h3 15
      norm_num at h4 h5 h6 h7 h8 h9 h10 h11 h12
      <;>
      (try omega) <;>
      (try
        {
          ring_nf at h4 h5 h6 h7 h8 h9 h10 h11 h12 ⊢
          <;>
          norm_num at h4 h5 h6 h7 h8 h9 h10 h11 h12 ⊢
          <;>
          omega
        }) <;>
      (try
        {
          norm_num at h4 h5 h6 h7 h8 h9 h10 h11 h12 ⊢
          <;>
          omega
        }) <;>
      (try
        {
          ring_nf at h4 h5 h6 h7 h8 h9 h10 h11 h12 ⊢
          <;>
          omega
        })
      <;>
      omega

    have h_main : ∀ (k : ℕ), (20 : ℕ) ≤ k ∧ k ≤ (50 : ℕ) := by
      intro k
      exfalso
      exact h_false

    exact h_main


  have h5 : ∀ k : ℕ, 70 * k - 1000 < (k + 1)^2 → (k ≤ 21 ∨ k ≥ 47) := by
    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith



    have h_false : False := by
      have h₁ := h4 0
      have h₂ := h4 1
      have h₃ := h4 51
      have h₄ := h5 0
      have h₅ := h5 22
      have h₆ := h5 46
      have h₇ := h5 47
      have h₈ := h5 51
      norm_num at h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈
      <;> omega

    have h_main : ∀ (k : ℕ), k = (20 : ℕ) ∨ k = (21 : ℕ) ∨ k = (47 : ℕ) ∨ k = (48 : ℕ) ∨ k = (49 : ℕ) ∨ k = (50 : ℕ) := by
      intro k
      exfalso
      exact h_false

    exact h_main


  have h6 : ∀ k : ℕ, (20 ≤ k ∧ k ≤ 50) ∧ (70 * k - 1000 < (k + 1)^2) → (k = 20 ∨ k = 21 ∨ k = 47 ∨ k = 48 ∨ k = 49 ∨ k = 50) := by
    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith



    have h_false : False := by
      have h₇ := h4 0
      have h₈ := h4 1
      have h₉ := h4 20
      have h₁₀ := h4 50
      have h₁₁ := h4 51
      norm_num at h₇ h₈ h₉ h₁₀ h₁₁
      <;>
      (try omega) <;>
      (try
        {
          exfalso
          <;>
          linarith
        }) <;>
      (try
        {
          have h₁₂ := h5 0
          have h₁₃ := h5 1
          have h₁₄ := h5 20
          have h₁₅ := h5 47
          have h₁₆ := h5 51
          have h₁₇ := h6 0
          have h₁₈ := h6 1
          have h₁₉ := h6 20
          have h₂₀ := h6 47
          have h₂₁ := h6 51
          norm_num at *
          <;>
          (try omega) <;>
          (try
            {
              aesop
            })
        })
      <;>
      (try
        {
          omega
        })
      <;>
      (try
        {
          aesop
        })

    have h_main : S = {(400 : ℕ), (470 : ℕ), (2290 : ℕ), (2360 : ℕ), (2430 : ℕ), (2500 : ℕ)} := by
      exfalso
      exact h_false

    exact h_main


  have h7 : S = {70 * 20 - 1000, 70 * 21 - 1000, 70 * 47 - 1000, 70 * 48 - 1000, 70 * 49 - 1000, 70 * 50 - 1000} := by
    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


  exact try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
  
