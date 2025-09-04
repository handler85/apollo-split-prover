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
theorem mathd_algebra_158 (a : ℕ) (h₀ : Even a)
    (h₁ : ∑ k in Finset.range 8, (2 * k + 1) - ∑ k in Finset.range 5, (a + 2 * k) = (4 : ℤ)) :
    a = 8 := by
  have h_sum_odds : ∑ k in Finset.range 8, (2 * k + 1) = 64 := by
    simp [Finset.sum_range_succ, mul_add, mul_one, add_assoc]
    <;> norm_num
    <;> rfl
  have h_sum_evens : ∑ k in Finset.range 5, (a + 2 * k) = 5 * a + 20 := by
    simp [Finset.sum_range_succ, mul_add, mul_one, add_assoc, add_comm, add_left_comm]
    <;> ring_nf at *
    <;> omega
  have h_main : a = 8 := by
    have h₂ : (∑ k in Finset.range 8, (2 * k + 1) : ℤ) - ∑ k in Finset.range 5, (a + 2 * k : ℤ) = 4 := by
      norm_cast at h₁ ⊢
      <;> simp_all [h_sum_odds, h_sum_evens]
      <;> ring_nf at *
      <;> omega
    have h₃ : (∑ k in Finset.range 8, (2 * k + 1) : ℤ) = 64 := by
      norm_num [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
      <;> rfl
    have h₄ : (∑ k in Finset.range 5, (a + 2 * k : ℤ)) = (5 * a + 20 : ℤ) := by
      simp [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
      <;> ring_nf
      <;> norm_cast
      <;> omega
    rw [h₃, h₄] at h₂
    have h₅ : (64 : ℤ) - (5 * a + 20 : ℤ) = 4 := by
      linarith
    have h₆ : a ≤ 16 := by
      by_contra h
      have h₇ : a ≥ 17  := by
        omega
      have h₈ : (5 * a + 20 : ℤ) ≥ 5 * 17 + 20 := by
        norm_cast
        <;> omega
      have h₉ : (64 : ℤ) - (5 * a + 20 : ℤ) ≤ 64 - (5 * 17 + 20 : ℤ) := by
        omega
      norm_num at h₉ ⊢
      <;> omega
    interval_cases a <;> norm_num at h₅ ⊢ <;>
    (try omega) <;>
    (try {
      simp_all [Int.ofNat_eq_coe]
      <;> omega
    }) <;>
    (try {
      norm_num at h₀ ⊢ <;>
      simp_all [Int.ofNat_eq_coe, even_iff_two_dvd]
      <;> omega
    })
    <;>
    omega
  exact h_main