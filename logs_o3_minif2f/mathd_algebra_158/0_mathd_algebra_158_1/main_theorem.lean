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

lemma mathd_algebra_158_1
  (a : ℕ)
  (h₀ : Even a)
  (h₁ :
  (↑(∑ k ∈ Finset.range (8 : ℕ), ((2 : ℕ) * k + (1 : ℕ))) : ℤ) -
      (↑(∑ k ∈ Finset.range (5 : ℕ), (a + (2 : ℕ) * k)) : ℤ) =
    (4 : ℤ)) :
  ∑ k ∈ Finset.range (8 : ℕ), ((2 : ℕ) * k + (1 : ℕ)) = (64 : ℕ) := by
  have h_sum_main : ∑ k ∈ Finset.range (8 : ℕ), ((2 : ℕ) * k + (1 : ℕ)) = 64 := by
    decide
  rw [h_sum_main]
  <;> norm_num
  <;>
  (try omega) <;>
  (try
    {
      simp_all [Finset.sum_range_succ, mul_add, mul_one, mul_comm, mul_left_comm, mul_assoc,
        Int.ofNat_add, Int.ofNat_mul, Int.ofNat_sub]
      <;>
      ring_nf at *
      <;>
      norm_cast at *
      <;>
      omega
    }) <;>
  (try omega)
  <;>
  (try
    {
      rcases h₀ with ⟨k, rfl⟩
      <;>
      simp_all [Finset.sum_range_succ, mul_add, mul_one, mul_comm, mul_left_comm, mul_assoc,
        Int.ofNat_add, Int.ofNat_mul, Int.ofNat_sub]
      <;>
      ring_nf at *
      <;>
      norm_cast at *
      <;>
      omega
    })
  <;>
  (try omega)
  <;>
  (try
    {
      norm_num [Finset.sum_range_succ, Finset.sum_range_zero] at *
      <;>
      ring_nf at *
      <;>
      omega
    })
  <;>
  (try omega)
  <;>
  (try
    {
      simp_all [Finset.sum_range_succ, mul_add, mul_one, mul_comm, mul_left_comm, mul_assoc,
        Int.ofNat_add, Int.ofNat_mul, Int.ofNat_sub]
      <;>
      ring_nf at *
      <;>
      norm_cast at *
      <;>
      omega
    })
  <;>
  (try omega)
