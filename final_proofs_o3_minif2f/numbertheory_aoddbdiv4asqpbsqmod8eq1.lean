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
theorem numbertheory_aoddbdiv4asqpbsqmod8eq1 (a : ℤ) (b : ℕ) (h₀ : Odd a) (h₁ : 4 ∣ b) :
    (a ^ 2 + b ^ 2) % 8 = 1 := by
  try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


  
  have h_a_sq : a ^ 2 % 8 = 1 := by
    have h₁ : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by
      cases' h₀ with k hk
      have h₂ : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by
        omega
      exact h₂
    rcases h₁ with (h₁ | h₁ | h₁ | h₁) <;>
    simp [h₁, pow_two, Int.mul_emod, Int.add_emod] <;>
    (try omega) <;>
    (try
      {
        norm_num
        <;>
        omega
      }) <;>
    (try
      {
        ring_nf
        <;>
        omega
      })
    <;>
    (try omega)
    <;>
    (try nlinarith)
  
  have h_b_sq : (b : ℤ) ^ 2 % 8 = 0 := by
    have h₂ : (4 : ℕ) ∣ b := h₁
    have h₃ : (b : ℤ) % 8 = 0 ∨ (b : ℤ) % 8 = 4 := by
      have h₄ : (4 : ℕ) ∣ b := h₁
      have h₅ : (b : ℤ) % 4 = 0 := by
        norm_cast
        omega
      have h₆ : (b : ℤ) % 8 = 0 ∨ (b : ℤ) % 8 = 4 := by
        omega
      exact h₆
    have h₄ : ((b : ℤ) ^ 2) % 8 = 0 := by
      rcases h₃ with (h₃ | h₃)
      · -- Case 1: b ≡ 0 mod 8
        have h₅ : (b : ℤ) % 8 = 0 := h₃
        have h₆ : ((b : ℤ) ^ 2) % 8 = 0 := by
          simp [h₅, pow_two, Int.mul_emod]
        exact h₆
      · -- Case 2: b ≡ 4 mod 8
        have h₅ : (b : ℤ) % 8 = 4 := h₃
        have h₆ : ((b : ℤ) ^ 2) % 8 = 0 := by
          simp [h₅, pow_two, Int.mul_emod]
        exact h₆
    exact h₄
  
  have h_main : (a ^ (2 : ℕ) + (↑b : ℤ) ^ (2 : ℕ)) % (8 : ℤ) = (1 : ℤ) := by
    have h₃ : (a ^ (2 : ℕ) : ℤ) % 8 = 1 := by
      norm_cast
      <;> simpa using h_a_sq
    have h₄ : ((b : ℤ) ^ (2 : ℕ)) % 8 = 0 := by simpa using h_b_sq
    have h₅ : ((a ^ (2 : ℕ) + (↑b : ℤ) ^ (2 : ℕ)) : ℤ) % 8 = 1 := by
      have h₅₁ : ((a ^ (2 : ℕ) + (↑b : ℤ) ^ (2 : ℕ)) : ℤ) % 8 = ((a ^ (2 : ℕ) : ℤ) % 8 + ((b : ℤ) ^ (2 : ℕ)) % 8) % 8 := by
        simp [Int.add_emod]
      rw [h₅₁]
      have h₅₂ : ((a ^ (2 : ℕ) : ℤ) % 8) = 1 := by simpa using h₃
      have h₅₃ : (((b : ℤ) ^ (2 : ℕ)) % 8) = 0 := by simpa using h₄
      rw [h₅₂, h₅₃]
      <;> norm_num
      <;> omega
    simpa using h₅
  
  simpa using h_main


