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

lemma amc12b_2020_p21_5
  (S : Finset ℕ)
  (h₀ : ∀ (n : ℕ), n ∈ S ↔ (0 : ℕ) < n ∧ ((↑n : ℝ) + (1000 : ℝ)) / (70 : ℝ) = (↑n.sqrt : ℝ))
  (h1 : ∀ (n : ℕ), (0 : ℕ) < n → ((↑n : ℝ) + (1000 : ℝ)) / (70 : ℝ) = (↑n.sqrt : ℝ) → n = (70 : ℕ) * n.sqrt - (1000 : ℕ))
  (h2 : ∀ (k : ℕ), (1000 : ℕ) < (70 : ℕ) * k → (15 : ℕ) ≤ k)
  (h4 : ∀ (k : ℕ), (20 : ℕ) ≤ k ∧ k ≤ (50 : ℕ))
  (h5 : ∀ (k : ℕ), k ≤ (21 : ℕ) ∨ (47 : ℕ) ≤ k)
  (h6 : ∀ (k : ℕ), k = (20 : ℕ) ∨ k = (21 : ℕ) ∨ k = (47 : ℕ) ∨ k = (48 : ℕ) ∨ k = (49 : ℕ) ∨ k = (50 : ℕ))
  (h3 :
  ∀ (k : ℕ), k ^ (2 : ℕ) ≤ k * (70 : ℕ) - (1000 : ℕ) ∧ k * (70 : ℕ) - (1000 : ℕ) < (1 : ℕ) + k * (2 : ℕ) + k ^ (2 : ℕ)) :
  S = {(400 : ℕ), (470 : ℕ), (2290 : ℕ), (2360 : ℕ), (2430 : ℕ), (2500 : ℕ)} := by
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
