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

lemma mathd_numbertheory_541_1
  (m n : ℕ)
  (h₀ : (1 : ℕ) < m)
  (h₁ : (1 : ℕ) < n)
  (h₂ : m * n = (2005 : ℕ)) :
  m + n = (406 : ℕ) := by
  have h_main : m + n = 406 := by
    have h₃ : m ∣ 2005 := by
      use n
      linarith
    have h₄ : n ∣ 2005 := by
      use m
      linarith
    have h₅ : m ≤ 2005 := Nat.le_of_dvd (by norm_num) h₃
    have h₆ : n ≤ 2005 := Nat.le_of_dvd (by norm_num) h₄
    -- We now check all possible values of m and n that divide 2005 and are greater than 1
    have h₇ : m = 5 ∨ m = 401 ∨ m = 1 ∨ m = 2005 := by
      -- We know m divides 2005, so we check the possible values
      have h₇₁ : m ∣ 2005 := h₃
      have h₇₂ : m ≤ 2005 := h₅
      interval_cases m <;> norm_num at h₇₁ ⊢ <;>
        (try omega) <;> (try omega) <;> (try omega) <;> (try omega) <;> (try
        {
          omega
        }) <;> (try
        {
          omega
        }) <;> (try
        {
          omega
        })
      <;> omega
    have h₈ : n = 5 ∨ n = 401 ∨ n = 1 ∨ n = 2005 := by
      -- Similarly for n
      have h₈₁ : n ∣ 2005 := h₄
      have h₈₂ : n ≤ 2005 := h₆
      interval_cases n <;> norm_num at h₈₁ ⊢ <;>
        (try omega) <;> (try omega) <;> (try omega) <;> (try omega) <;> (try
        {
          omega
        }) <;> (try
        {
          omega
        }) <;> (try
        {
          omega
        })
      <;> omega
    -- We now check all combinations of m and n to find the correct ones
    rcases h₇ with (rfl | rfl | rfl | rfl) <;> rcases h₈ with (rfl | rfl | rfl | rfl) <;>
      norm_num at h₂ ⊢ <;>
      (try omega) <;> (try omega) <;> (try omega) <;> (try omega) <;> (try
      {
        aesop
      }) <;> (try
      {
        omega
      }) <;> (try
      {
        aesop
      })
    <;> omega
  exact h_main
