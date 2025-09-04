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
theorem amc12a_2021_p8 (d : ℕ → ℕ) 
    (h₀ : d 0 = 0) (h₁ : d 1 = 0) (h₂ : d 2 = 1) 
    (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3)) :
  Even (d 2021) ∧ Odd (d 2022) ∧ Even (d 2023) := by 
  have parity_rec : ∀ n ≥ 3, (d n % 2) = ((d (n - 1) % 2) + (d (n - 3) % 2)) % 2  := by
    intro n hn
    simp_all only [ge_iff_le, add_mod_mod, mod_add_mod]
  have base_cases : (d 0 % 2 = 0) ∧ (d 1 % 2 = 0) ∧ (d 2 % 2 = 1)  := by
    omega
  have small_values : (d 3 % 2 = 1) ∧ (d 4 % 2 = 1) ∧ (d 5 % 2 = 0) ∧ (d 6 % 2 = 1) ∧ (d 7 % 2 = 0)  := by
    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
  have periodicity : ∀ n ≥ 2, d (n + 7) % 2 = d n % 2  := by
    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


    
    have h_main : ∀ (n : ℕ), (2 : ℕ) ≤ n → (d ((2 : ℕ) + n) * (4 : ℕ) + d n * (5 : ℕ) + d (n - (2 : ℕ)) * (2 : ℕ)) % (2 : ℕ) = d n % (2 : ℕ) := by
      intro n hn
      have h₄ : (d ((2 : ℕ) + n) * (4 : ℕ) + d n * (5 : ℕ) + d (n - (2 : ℕ)) * (2 : ℕ)) % (2 : ℕ) = d n % (2 : ℕ) := by
        have h₅ : (d ((2 : ℕ) + n) * (4 : ℕ) + d n * (5 : ℕ) + d (n - (2 : ℕ)) * (2 : ℕ)) % (2 : ℕ) = (d ((2 : ℕ) + n) * (4 : ℕ) % 2 + d n * (5 : ℕ) % 2 + d (n - (2 : ℕ)) * (2 : ℕ) % 2) % 2 := by
          simp [Nat.add_mod, Nat.mul_mod]
          <;> omega
        rw [h₅]
        have h₆ : d ((2 : ℕ) + n) * (4 : ℕ) % 2 = 0 := by
          have h₇ : d ((2 : ℕ) + n) * (4 : ℕ) % 2 = 0 := by
            have h₈ : d ((2 : ℕ) + n) % 2 = 0 ∨ d ((2 : ℕ) + n) % 2 = 1 := by omega
            rcases h₈ with (h₈ | h₈) <;> simp [h₈, Nat.mul_mod, Nat.add_mod, Nat.mod_mod]
            <;> omega
          exact h₇
        have h₇ : d n * (5 : ℕ) % 2 = d n % 2 := by
          have h₈ : d n * (5 : ℕ) % 2 = d n % 2 := by
            have h₉ : d n % 2 = 0 ∨ d n % 2 = 1 := by omega
            rcases h₉ with (h₉ | h₉) <;> simp [h₉, Nat.mul_mod, Nat.add_mod, Nat.mod_mod] <;>
              (try omega) <;> (try omega) <;> (try omega) <;> (try omega)
            <;> (try omega)
            <;> (try omega)
            <;> omega
          exact h₈
        have h₈ : d (n - (2 : ℕ)) * (2 : ℕ) % 2 = 0 := by
          have h₉ : d (n - (2 : ℕ)) * (2 : ℕ) % 2 = 0 := by
            have h₁₀ : d (n - (2 : ℕ)) % 2 = 0 ∨ d (n - (2 : ℕ)) % 2 = 1 := by omega
            rcases h₁₀ with (h₁₀ | h₁₀) <;> simp [h₁₀, Nat.mul_mod, Nat.add_mod, Nat.mod_mod]
            <;> omega
          exact h₉
        omega
      exact h₄
    exact h_main


  have index_2021 : d 2021 % 2 = d 5 % 2  := by
    simp_all only [ge_iff_le, add_mod_mod, mod_add_mod, implies_true, zero_mod, mod_succ, and_self, le_refl, Nat.add_one_sub_one, tsub_self, add_zero, true_and, le_add_iff_nonneg_left, _root_.zero_le, add_tsub_cancel_right]
  have index_2022 : d 2022 % 2 = d 6 % 2  := by
    simp_all only [ge_iff_le, add_mod_mod, mod_add_mod, implies_true, zero_mod, mod_succ, and_self, le_refl, Nat.add_one_sub_one, tsub_self, add_zero, true_and, le_add_iff_nonneg_left, _root_.zero_le, add_tsub_cancel_right]
  have index_2023 : d 2023 % 2 = d 7 % 2  := by
    simp_all only [ge_iff_le, add_mod_mod, mod_add_mod, implies_true, zero_mod, mod_succ, and_self, le_refl, Nat.add_one_sub_one, tsub_self, add_zero, true_and, le_add_iff_nonneg_left, _root_.zero_le, add_tsub_cancel_right]
  have d2021_even : Even (d 2021)  := by
    simp_all only [ge_iff_le, add_mod_mod, mod_add_mod, implies_true, zero_mod, mod_succ, and_self, le_refl, Nat.add_one_sub_one, tsub_self, add_zero, true_and, le_add_iff_nonneg_left, _root_.zero_le, add_tsub_cancel_right]
  have d2022_odd : Odd (d 2022)  := by
    simp_all only [ge_iff_le, add_mod_mod, mod_add_mod, implies_true, zero_mod, mod_succ, and_self, le_refl, Nat.add_one_sub_one, tsub_self, add_zero, true_and, le_add_iff_nonneg_left, _root_.zero_le, add_tsub_cancel_right]
  have d2023_even : Even (d 2023)  := by
    simp_all only [ge_iff_le, add_mod_mod, mod_add_mod, implies_true, zero_mod, mod_succ, and_self, le_refl, Nat.add_one_sub_one, tsub_self, add_zero, true_and, le_add_iff_nonneg_left, _root_.zero_le, add_tsub_cancel_right]
  exact ⟨d2021_even, d2022_odd, d2023_even⟩