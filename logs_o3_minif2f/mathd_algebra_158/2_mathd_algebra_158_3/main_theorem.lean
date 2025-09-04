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

lemma mathd_algebra_158_3
  (a : ℕ)
  (h₀ : Even a)
  (h₁ :
  (↑(∑ k ∈ Finset.range (8 : ℕ), ((2 : ℕ) * k + (1 : ℕ))) : ℤ) -
      (↑(∑ k ∈ Finset.range (5 : ℕ), (a + (2 : ℕ) * k)) : ℤ) =
    (4 : ℤ))
  (h_sum_odd : ∑ k ∈ Finset.range (8 : ℕ), ((2 : ℕ) * k + (1 : ℕ)) = (64 : ℕ))
  (h_sum_even : ∑ k ∈ Finset.range (5 : ℕ), (a + (2 : ℕ) * k) = (5 : ℕ) * a + (20 : ℕ)) :
  (64 : ℕ) - ((5 : ℕ) * a + (20 : ℕ)) = (4 : ℕ) := by
  have h_main : (64 : ℕ) - ((5 : ℕ) * a + (20 : ℕ)) = (4 : ℕ) := by
    have h₂ := h₁
    simp [h_sum_odd, h_sum_even, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ] at h₂ ⊢
    <;>
    (try omega) <;>
    (try
      {
        norm_num at h₂ ⊢ <;>
        ring_nf at h₂ ⊢ <;>
        norm_cast at h₂ ⊢ <;>
        omega
      }) <;>
    (try
      {
        rcases h₀ with ⟨k, rfl⟩
        norm_num at h₂ ⊢ <;>
        ring_nf at h₂ ⊢ <;>
        norm_cast at h₂ ⊢ <;>
        omega
      }) <;>
    (try
      {
        rcases h₀ with ⟨k, rfl⟩
        norm_num at h₂ ⊢ <;>
        ring_nf at h₂ ⊢ <;>
        norm_cast at h₂ ⊢ <;>
        ring_nf at h₂ ⊢ <;>
        omega
      })
    <;>
    omega
  exact h_main
