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

lemma mathd_numbertheory_135_1
  (n A B C : ℕ)
  (h₀ : n = (129199212 : ℕ))
  (h₁ : (11 : ℕ) ∣ (129199213 : ℕ))
  (h₂ : (¬A = B ∧ ¬A = C) ∧ ¬B = C)
  (h₃ : {A, B, C} ⊂ Finset.Icc (0 : ℕ) C)
  (h₄ : Odd A ∧ Odd C)
  (h₅ : ¬(3 : ℕ) ∣ B)
  (h₆ : (2 : ℕ) = B ∧ (1 : ℕ) = A ∧ (2 : ℕ) = B ∧ (9 : ℕ) = C ∧ (1 : ℕ) = A ∧ (9 : ℕ) = C ∧ (2 : ℕ) = B ∧ (1 : ℕ) = A) :
  digits (10 : ℕ) (129199212 : ℕ) = [B, A, B, C, C, A, C, B, A] := by
  have h_main : digits (10 : ℕ) (129199212 : ℕ) = [B, A, B, C, C, A, C, B, A] := by
    have h₇ := h₆.1
    have h₈ := h₆.2.1
    have h₉ := h₆.2.2.1
    have h₁₀ := h₆.2.2.2.1
    have h₁₁ := h₆.2.2.2.2.1
    have h₁₂ := h₆.2.2.2.2.2.1
    have h₁₃ := h₆.2.2.2.2.2.2.1
    have h₁₄ := h₆.2.2.2.2.2.2.2
    have h₁₅ := h₆.2.2.2.2.2.2.2
    simp at h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ h₁₃ h₁₄ h₁₅
    <;>
    (try omega) <;>
    (try
      {
        norm_num [digits_zero] at *
        <;>
        (try contradiction) <;>
        (try omega) <;>
        (try
          {
            rcases C with (_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | C) <;>
            rcases A with (_ | _ | _ | A) <;>
            rcases B with (_ | _ | _ | B) <;>
            norm_num [digits_zero] at * <;>
            simp_all (config := {decide := true}) <;>
            omega
          }) <;>
        (try
          {
            aesop
          })
      }) <;>
    (try
      {
        aesop
      }) <;>
    (try
      {
        norm_num [digits_zero] at * <;>
        rcases C with (_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | C) <;>
        rcases A with (_ | _ | _ | A) <;>
        rcases B with (_ | _ | _ | B) <;>
        norm_num [digits_zero] at * <;>
        simp_all (config := {decide := true}) <;>
        aesop
      })
    <;>
    (try omega) <;>
    (try aesop)
    <;>
    (try norm_num [digits_zero] at *) <;>
    (try omega) <;>
    (try aesop)
    <;>
    (try omega)
    <;>
    (try aesop)
    <;>
    (try omega)
    <;>
    (try aesop)
    <;>
    (try omega)
    <;>
    (try aesop)
    <;>
    (try omega)
    <;>
    (try aesop)
  
  exact h_main
