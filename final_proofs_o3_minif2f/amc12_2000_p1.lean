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
theorem amc12_2000_p1 (i m o : ℕ)
    (h₀ : i ≠ m ∧ m ≠ o ∧ o ≠ i)
    (h₁ : i * m * o = 2001) :
    i + m + o ≤ 671 := by
  try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


  
  have h_main : i + m + o ≤ 671 := by
    have h₂ : i ∣ 2001 := by
      use m * o
      linarith
    have h₃ : m ∣ 2001 := by
      use i * o
      linarith
    have h₄ : o ∣ 2001 := by
      use i * m
      linarith
    have h₅ : i = 1 ∨ i = 3 ∨ i = 23 ∨ i = 29 ∨ i = 69 ∨ i = 87 ∨ i = 667 ∨ i = 2001 := by
      have h₅₁ : i ∣ 2001 := h₂
      have h₅₂ : i ≤ 2001 := Nat.le_of_dvd (by norm_num) h₅₁
      interval_cases i <;> norm_num at h₅₁ ⊢ <;> try { omega } <;> try {
        aesop
      }
    have h₆ : m = 1 ∨ m = 3 ∨ m = 23 ∨ m = 29 ∨ m = 69 ∨ m = 87 ∨ m = 667 ∨ m = 2001 := by
      have h₆₁ : m ∣ 2001 := h₃
      have h₆₂ : m ≤ 2001 := Nat.le_of_dvd (by norm_num) h₆₁
      interval_cases m <;> norm_num at h₆₁ ⊢ <;> try { omega } <;> try {
        aesop
      }
    have h₇ : o = 1 ∨ o = 3 ∨ o = 23 ∨ o = 29 ∨ o = 69 ∨ o = 87 ∨ o = 667 ∨ o = 2001 := by
      have h₇₁ : o ∣ 2001 := h₄
      have h₇₂ : o ≤ 2001 := Nat.le_of_dvd (by norm_num) h₇₁
      interval_cases o <;> norm_num at h₇₁ ⊢ <;> try { omega } <;> try {
        aesop
      }
    rcases h₅ with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    rcases h₆ with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    rcases h₇ with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    norm_num at h₁ h₀ ⊢ <;>
    (try omega) <;>
    (try
      {
        simp_all (config := {decide := true})
        <;>
        omega
      }) <;>
    (try
      {
        norm_num at h₁ h₀ ⊢ <;>
        simp_all (config := {decide := true}) <;>
        omega
      }) <;>
    (try
      {
        aesop
      }) <;>
    (try
      {
        norm_num at h₁ h₀ ⊢ <;>
        simp_all (config := {decide := true}) <;>
        omega
      })
    <;>
    aesop
  
  exact h_main


