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

lemma mathd_algebra_289_3
  (k t m n : ℕ)
  (h₀ : Nat.Prime m ∧ Nat.Prime n)
  (h₁ : t < k)
  (h₂ : (↑k : ℤ) ^ (2 : ℕ) - (↑m : ℤ) * (↑k : ℤ) + (↑n : ℤ) = (0 : ℤ))
  (h₃ : (↑t : ℤ) ^ (2 : ℕ) - (↑m : ℤ) * (↑t : ℤ) + (↑n : ℤ) = (0 : ℤ))
  (sum_roots : k + t = m)
  (prod_roots : k * t = n) :
  t = (1 : ℕ) ∨ k = (1 : ℕ) := by
  have h_main : t = (1 : ℕ) ∨ k = (1 : ℕ) := by
    by_contra! h
    have h₄ : k > 1 := by
      by_contra h₅
      have h₆ : k = 0 ∨ k = 1 := by omega
      cases h₆ with
      | inl h₆ =>
        simp [h₆] at h₁ h₂ h₃ sum_roots prod_roots h₀
        <;>
        (try omega) <;>
        (try nlinarith) <;>
        (try aesop)
      | inr h₆ =>
        aesop
    have h₅ : t > 1 := by
      by_contra h₅
      have h₆ : t = 0 ∨ t = 1 := by omega
      cases h₆ with
      | inl h₆ =>
        simp [h₆] at h₁ h₂ h₃ sum_roots prod_roots h₀
        <;>
        (try omega) <;>
        (try nlinarith) <;>
        (try aesop)
      | inr h₆ =>
        aesop
    have h₆ : n = k * t := by
      rw [prod_roots]
    have h₇ : m = k + t := by
      omega
    have h₈ : Nat.Prime n := h₀.2
    have h₉ : Nat.Prime m := h₀.1
    have h₁₀ : k > 0 := by omega
    have h₁₁ : t > 0 := by omega
    have h₁₂ : n > 1 := Nat.Prime.one_lt h₈
    have h₁₃ : m > 1 := Nat.Prime.one_lt h₉
    have h₁₄ : k * t > 1 := by
      nlinarith
    have h₁₅ : k * t = n := by
      rw [prod_roots]
    have h₁₆ : k ∣ n := by
      use t
      <;> linarith
    have h₁₇ : k = n := by
      have h₁₈ := Nat.Prime.eq_one_or_self_of_dvd h₈ k h₁₆
      cases h₁₈ with
      | inl h₁₈ =>
        exfalso
        linarith
      | inr h₁₈ =>
        nlinarith
    nlinarith [Nat.Prime.two_le h₈]
  exact h_main
