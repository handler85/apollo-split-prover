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

lemma imo_1982_p1_1
  (f : ℕ → ℕ)
  (h₁ : f (2 : ℕ) = (0 : ℕ))
  (h₂ : (0 : ℕ) < f (3 : ℕ))
  (h₃ : f (9999 : ℕ) = (3333 : ℕ))
  (h₀ :
  ∀ (m n : ℕ),
    (0 : ℕ) < m →
      (0 : ℕ) < n → (↑(f (m + n)) : ℤ) + (-(↑(f m) : ℤ) - (↑(f n) : ℤ)) = (0 : ℤ) ∨ f (m + n) - f m - f n = (1 : ℕ)) :
  f (1 : ℕ) = (0 : ℕ) := by
  have h_f1 : f (1 : ℕ) = 0 := by
    have h₄ := h₀ 1 1 (by decide) (by decide)
    cases h₄ with
    | inl h₄ =>
      -- Case: (f (m + n) : ℤ) + (-(f m : ℤ) - (f n : ℤ)) = 0
      simp [h₁, h₂, h₃, Nat.cast_add, Nat.cast_one, Nat.cast_zero, Nat.cast_mul] at h₄
      <;>
      (try omega) <;>
      (try norm_num at h₄ ⊢) <;>
      (try simp_all [Nat.cast_add, Nat.cast_one, Nat.cast_zero, Nat.cast_mul]) <;>
      (try omega) <;>
      (try ring_nf at h₄ ⊢) <;>
      (try omega)
    | inr h₄ =>
      -- Case: f (m + n) - f m - f n = 1
      have h₅ := h₄
      simp [h₁, h₂, h₃, Nat.sub_eq_zero_of_le] at h₅ ⊢
      <;>
      (try omega) <;>
      (try norm_num at h₅ ⊢) <;>
      (try simp_all [Nat.cast_add, Nat.cast_one, Nat.cast_zero, Nat.cast_mul]) <;>
      (try omega) <;>
      (try ring_nf at h₅ ⊢) <;>
      (try omega)
      <;>
      omega
  exact h_f1
