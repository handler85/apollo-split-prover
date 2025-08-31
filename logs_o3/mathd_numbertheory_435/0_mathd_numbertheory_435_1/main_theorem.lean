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

lemma mathd_numbertheory_435_1
  (k : ℕ)
  (h₀ : (0 : ℕ) < k)
  (h₁ : ∀ (n : ℕ), ((6 : ℕ) * n + k).gcd ((6 : ℕ) * n + (3 : ℕ)) = (1 : ℕ))
  (h₂ : ∀ (n : ℕ), ((6 : ℕ) * n + k).gcd ((6 : ℕ) * n + (2 : ℕ)) = (1 : ℕ))
  (h₃ : ∀ (n : ℕ), ((6 : ℕ) * n + k).gcd ((6 : ℕ) * n + (1 : ℕ)) = (1 : ℕ)) :
  k.gcd (3 : ℕ) = (1 : ℕ) := by
  have h_main : k.gcd (3 : ℕ) = (1 : ℕ) := by
    have h₄ := h₁ 0
    have h₅ := h₁ 1
    have h₆ := h₁ k
    have h₇ := h₂ 0
    have h₈ := h₂ 1
    have h₉ := h₂ k
    have h₁₀ := h₃ 0
    have h₁₁ := h₃ 1
    have h₁₂ := h₃ k
    simp at h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂
    <;>
    (try omega) <;>
    (try
      {
        simp_all [Nat.gcd_eq_right, Nat.gcd_eq_left]
        <;>
        aesop
      }) <;>
    (try
      {
        norm_num at *
        <;>
        aesop
      }) <;>
    (try
      {
        ring_nf at *
        <;>
        aesop
      }) <;>
    (try
      {
        simp_all [Nat.gcd_eq_right, Nat.gcd_eq_left]
        <;>
        omega
      })
    <;>
    aesop
  
  exact h_main
