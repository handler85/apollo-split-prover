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

lemma mathd_algebra_276_1
  (a b : ℤ)
  (h₀ : ∀ (x : ℝ), (10 : ℝ) * x ^ (2 : ℕ) - x - (24 : ℝ) = ((↑a : ℝ) * x - (8 : ℝ)) * ((↑b : ℝ) * x + (3 : ℝ))) :
  ∀ (x : ℝ),
    (10 : ℝ) * x ^ (2 : ℕ) - x = (↑a : ℝ) * (↑b : ℝ) * x ^ (2 : ℕ) + ((3 : ℝ) * (↑a : ℝ) - (8 : ℝ) * (↑b : ℝ)) * x := by
  have h_main : ∀ (x : ℝ), (10 : ℝ) * x ^ (2 : ℕ) - x = (↑a : ℝ) * (↑b : ℝ) * x ^ (2 : ℕ) + ((3 : ℝ) * (↑a : ℝ) - (8 : ℝ) * (↑b : ℝ)) * x := by
    intro x
    have h₁ := h₀ x
    have h₂ := h₀ 0
    have h₃ := h₀ 1
    have h₄ := h₀ (-1)
    have h₅ := h₀ (1 / 2)
    have h₆ := h₀ (-1 / 2)
    norm_num at h₁ h₂ h₃ h₄ h₅ h₆
    ring_nf at h₁ h₂ h₃ h₄ h₅ h₆ ⊢
    field_simp at h₁ h₂ h₃ h₄ h₅ h₆ ⊢
    norm_cast at h₁ h₂ h₃ h₄ h₅ h₆ ⊢
    <;>
    (try ring_nf at h₁ h₂ h₃ h₄ h₅ h₆ ⊢) <;>
    (try norm_cast at h₁ h₂ h₃ h₄ h₅ h₆ ⊢) <;>
    (try simp_all [mul_comm, mul_assoc, mul_left_comm]) <;>
    (try ring_nf at * ) <;>
    (try norm_num at * ) <;>
    (try nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1), sq_nonneg (x - 1 / 2), sq_nonneg (x + 1 / 2)]) <;>
    (try omega) <;>
    (try linarith)
    <;>
    nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1), sq_nonneg (x - 1 / 2), sq_nonneg (x + 1 / 2)]
  
  exact h_main
