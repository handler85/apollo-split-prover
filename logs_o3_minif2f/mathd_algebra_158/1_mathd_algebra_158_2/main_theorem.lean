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

lemma mathd_algebra_158_2
  (a : ℕ)
  (h₀ : Even a)
  (h₁ :
  (↑(∑ k ∈ Finset.range (8 : ℕ), ((2 : ℕ) * k + (1 : ℕ))) : ℤ) -
      (↑(∑ k ∈ Finset.range (5 : ℕ), (a + (2 : ℕ) * k)) : ℤ) =
    (4 : ℤ))
  (h_sum_odd : ∑ k ∈ Finset.range (8 : ℕ), ((2 : ℕ) * k + (1 : ℕ)) = (64 : ℕ)) :
  ∑ k ∈ Finset.range (5 : ℕ), (a + (2 : ℕ) * k) = (5 : ℕ) * a + (20 : ℕ) := by
  have h_sum_range_8 : (∑ k ∈ Finset.range (8 : ℕ), ((2 : ℕ) * k + (1 : ℕ))) = 64 := by
    simp [Finset.sum_range_succ, mul_add, mul_one, add_assoc]
    <;> norm_num
    <;> rfl
  
  have h_sum_goal : ∑ k ∈ Finset.range (5 : ℕ), (a + (2 : ℕ) * k) = (5 : ℕ) * a + (20 : ℕ) := by
    simp [Finset.sum_range_succ, mul_add, mul_one, add_assoc] at h₁ ⊢
    <;> ring_nf at h₁ ⊢ <;>
    (try omega) <;>
    (try
      {
        norm_num at h₁ ⊢ <;>
        rcases h₀ with ⟨k, hk⟩ <;>
        simp [hk, mul_add, mul_comm, mul_left_comm, mul_assoc, Nat.mul_sub_left_distrib, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at h₁ ⊢ <;>
        ring_nf at h₁ ⊢ <;>
        omega
      }) <;>
    (try omega) <;>
    (try
      {
        omega
      })
    <;>
    omega
  
  exact h_sum_goal
