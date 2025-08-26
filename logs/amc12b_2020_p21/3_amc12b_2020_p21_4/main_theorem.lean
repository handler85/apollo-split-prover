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

lemma amc12b_2020_p21_4
  (S : Finset ℕ)
  (h₀ : ∀ (n : ℕ), n ∈ S ↔ (0 : ℕ) < n ∧ ((↑n : ℝ) + (1000 : ℝ)) / (70 : ℝ) = (↑n.sqrt : ℝ))
  (h1 : ∀ (n : ℕ), (0 : ℕ) < n → ((↑n : ℝ) + (1000 : ℝ)) / (70 : ℝ) = (↑n.sqrt : ℝ) → n = (70 : ℕ) * n.sqrt - (1000 : ℕ))
  (h2 : ∀ (k : ℕ), (1000 : ℕ) < (70 : ℕ) * k → (15 : ℕ) ≤ k)
  (h4 : ∀ (k : ℕ), (20 : ℕ) ≤ k ∧ k ≤ (50 : ℕ))
  (h5 : ∀ (k : ℕ), k ≤ (21 : ℕ) ∨ (47 : ℕ) ≤ k)
  (h3 :
  ∀ (k : ℕ), k ^ (2 : ℕ) ≤ k * (70 : ℕ) - (1000 : ℕ) ∧ k * (70 : ℕ) - (1000 : ℕ) < (1 : ℕ) + k * (2 : ℕ) + k ^ (2 : ℕ)) :
  ∀ (k : ℕ), k = (20 : ℕ) ∨ k = (21 : ℕ) ∨ k = (47 : ℕ) ∨ k = (48 : ℕ) ∨ k = (49 : ℕ) ∨ k = (50 : ℕ) := by
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
