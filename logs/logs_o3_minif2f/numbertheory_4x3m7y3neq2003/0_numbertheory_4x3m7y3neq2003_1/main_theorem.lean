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

lemma numbertheory_4x3m7y3neq2003_1
  (x y : ℤ)
  (h : (4 : ℤ) * x ^ (3 : ℕ) - (7 : ℤ) * y ^ (3 : ℕ) = (2003 : ℤ))
  (h4x3_mod7 : (4 : ℤ) * x ^ (3 : ℕ) % (7 : ℤ) = (1 : ℤ)) :
  ∀ (z : ℤ), (7 : ℤ) ∣ z ^ (3 : ℕ) ∨ z ^ (3 : ℕ) % (7 : ℤ) = (1 : ℤ) ∨ z ^ (3 : ℕ) % (7 : ℤ) = (6 : ℤ) := by
  have h_main : ∀ (z : ℤ), (7 : ℤ) ∣ z ^ (3 : ℕ) ∨ z ^ (3 : ℕ) % (7 : ℤ) = (1 : ℤ) ∨ z ^ (3 : ℕ) % (7 : ℤ) = (6 : ℤ) := by
    intro z
    have h₁ : z ^ 3 % 7 = 0 ∨ z ^ 3 % 7 = 1 ∨ z ^ 3 % 7 = 6 := by
      have h₂ : z % 7 = 0 ∨ z % 7 = 1 ∨ z % 7 = 2 ∨ z % 7 = 3 ∨ z % 7 = 4 ∨ z % 7 = 5 ∨ z % 7 = 6 := by omega
      rcases h₂ with (h₂ | h₂ | h₂ | h₂ | h₂ | h₂ | h₂)
      · -- Case z ≡ 0 mod 7
        have h₃ : z ^ 3 % 7 = 0 := by
          have h₄ : z % 7 = 0 := h₂
          have h₅ : z ^ 3 % 7 = 0 := by
            simp [h₄, pow_three, Int.mul_emod, Int.emod_emod]
            <;> norm_num
          exact h₅
        omega
      · -- Case z ≡ 1 mod 7
        have h₃ : z ^ 3 % 7 = 1 := by
          have h₄ : z % 7 = 1 := h₂
          have h₅ : z ^ 3 % 7 = 1 := by
            simp [h₄, pow_three, Int.mul_emod, Int.emod_emod]
            <;> norm_num
          exact h₅
        omega
      · -- Case z ≡ 2 mod 7
        have h₃ : z ^ 3 % 7 = 1 := by
          have h₄ : z % 7 = 2 := h₂
          have h₅ : z ^ 3 % 7 = 1 := by
            simp [h₄, pow_three, Int.mul_emod, Int.emod_emod]
            <;> norm_num
          exact h₅
        omega
      · -- Case z ≡ 3 mod 7
        have h₃ : z ^ 3 % 7 = 6 := by
          have h₄ : z % 7 = 3 := h₂
          have h₅ : z ^ 3 % 7 = 6 := by
            simp [h₄, pow_three, Int.mul_emod, Int.emod_emod]
            <;> norm_num
          exact h₅
        omega
      · -- Case z ≡ 4 mod 7
        have h₃ : z ^ 3 % 7 = 1 := by
          have h₄ : z % 7 = 4 := h₂
          have h₅ : z ^ 3 % 7 = 1 := by
            simp [h₄, pow_three, Int.mul_emod, Int.emod_emod]
            <;> norm_num
          exact h₅
        omega
      · -- Case z ≡ 5 mod 7
        have h₃ : z ^ 3 % 7 = 6 := by
          have h₄ : z % 7 = 5 := h₂
          have h₅ : z ^ 3 % 7 = 6 := by
            simp [h₄, pow_three, Int.mul_emod, Int.emod_emod]
            <;> norm_num
          exact h₅
        omega
      · -- Case z ≡ 6 mod 7
        have h₃ : z ^ 3 % 7 = 6 := by
          have h₄ : z % 7 = 6 := h₂
          have h₅ : z ^ 3 % 7 = 6 := by
            simp [h₄, pow_three, Int.mul_emod, Int.emod_emod]
            <;> norm_num
          exact h₅
        omega
    rcases h₁ with (h₁ | h₁ | h₁)
    · -- Case z^3 ≡ 0 mod 7
      exact Or.inl (by omega)
    · -- Case z^3 ≡ 1 mod 7
      exact Or.inr (Or.inl (by omega))
    · -- Case z^3 ≡ 6 mod 7
      exact Or.inr (Or.inr (by omega))
  
  exact h_main
