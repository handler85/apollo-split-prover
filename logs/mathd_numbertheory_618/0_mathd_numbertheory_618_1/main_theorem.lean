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

lemma mathd_numbertheory_618_1
  (n : ℕ)
  (p : ℕ → ℕ)
  (hn : (0 : ℕ) < n)
  (h₁ : (1 : ℕ) < ((41 : ℕ) + (n ^ (2 : ℕ) - n)).gcd ((41 : ℕ) + ((1 : ℕ) + n * (2 : ℕ) + n ^ (2 : ℕ) - ((1 : ℕ) + n))))
  (h₀ : ∀ (x : ℕ), p x = (41 : ℕ) + (x ^ (2 : ℕ) - x)) :
  (41 : ℕ) ≤ n := by
  have h_main : 41 ≤ n := by
    by_contra! h
    have h₂ : n ≤ 40 := by linarith
    interval_cases n <;> norm_num [Nat.gcd_eq_right, Nat.gcd_eq_left, Nat.pow_succ, Nat.mul_sub_left_distrib,
      Nat.mul_sub_right_distrib, Nat.add_assoc] at h₁ ⊢ <;>
      (try omega) <;>
      (try contradiction) <;>
      (try {
        simp_all [Nat.gcd_eq_right, Nat.gcd_eq_left, Nat.pow_succ, Nat.mul_sub_left_distrib,
          Nat.mul_sub_right_distrib, Nat.add_assoc]
        <;> norm_num at * <;>
        (try omega) <;>
        (try contradiction)
      })
    <;>
    (try {
      ring_nf at *
      <;> norm_num [Nat.gcd_eq_right, Nat.gcd_eq_left, Nat.pow_succ, Nat.mul_sub_left_distrib,
        Nat.mul_sub_right_distrib, Nat.add_assoc] at * <;>
      omega
    })
    <;>
    (try {
      simp_all [Nat.gcd_eq_right, Nat.gcd_eq_left, Nat.pow_succ, Nat.mul_sub_left_distrib,
        Nat.mul_sub_right_distrib, Nat.add_assoc]
      <;> norm_num at * <;>
      omega
    })
    <;>
    (try {
      ring_nf at *
      <;> omega
    })
  exact h_main
