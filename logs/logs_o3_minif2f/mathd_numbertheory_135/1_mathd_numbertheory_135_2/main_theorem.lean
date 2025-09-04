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
lemma mathd_numbertheory_135_2
    (n A B C : ℕ)
    (h₀ : n = (129199212 : ℕ))
    (h₁ : (11 : ℕ) ∣ (129199213 : ℕ))
    (h₂ : (¬A = B ∧ ¬A = C) ∧ ¬B = C)
    (h₃ : {A, B, C} ⊂ Finset.Icc (0 : ℕ) C)
    (h₄ : Odd A ∧ Odd C)
    (h₅ : ¬(3 : ℕ) ∣ B)
    (h₆ : (2 : ℕ) = B ∧ (1 : ℕ) = A ∧ (2 : ℕ) = B ∧ (9 : ℕ) = C ∧ (1 : ℕ) = A ∧ (9 : ℕ) = C ∧ (2 : ℕ) = B ∧ (1 : ℕ) = A)
    (h_digits : digits (10 : ℕ) (129199212 : ℕ) = [B, A, B, C, C, A, C, B, A]) :
    A * (100 : ℕ) + B * (10 : ℕ) + C = (129 : ℕ) := by
    --have h_contradiction : False := by
        --
        --
        --
        --
        --
        --
        --
        --
        --
        --
        --<;>
        (try omega) <;>
        (try
            {
                omega
            }) <;>
        (try
            {
                omega
            }) <;>
        (try
            {
                norm_num [Nat.dvd_iff_mod_eq_zero, Nat.mod_eq_of_lt] at h₁
                <;> omega
            })
        <;>
        (try
            {
                simp_all [Nat.odd_iff_not_even, Nat.even_iff]
                <;> omega
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
        <;>
        (try
            {
                omega
            })
  
  