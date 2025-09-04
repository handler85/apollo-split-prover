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

lemma mathd_numbertheory_34_2
  (x k m : ℕ)
  (lemma6 : x = m * (100 : ℕ) - (11 : ℕ))
  (hk' : k = m * (9 : ℕ) - (1 : ℕ))
  (lemma4 : ((1 : ℕ) + (m * (9 : ℕ) - (1 : ℕ))) % (9 : ℕ) = (0 : ℕ))
  (hk : (m * (100 : ℕ) - (11 : ℕ)) * (9 : ℕ) = (1 : ℕ) + (m * (9 : ℕ) - (1 : ℕ)) * (100 : ℕ))
  (h₁ : (m * (100 : ℕ) - (11 : ℕ)) * (9 : ℕ) % (100 : ℕ) = (1 : ℕ))
  (h₀ : m * (100 : ℕ) - (11 : ℕ) < (100 : ℕ)) :
  m = (1 : ℕ) := by
  have h_main : m ≤ 1 := by
    by_contra! h
    have h₂ : m ≥ 2 := by omega
    have h₃ : m * 100 ≥ 200 := by
      nlinarith
    have h₄ : m * 100 - 11 ≥ 189 := by
      omega
    have h₅ : m * 100 - 11 < 100 := by
      omega
    omega
  
  have h_final : m = 1 := by
    interval_cases m <;> norm_num [Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib, Nat.add_sub_assoc] at * <;>
      (try omega) <;>
      (try ring_nf at *) <;>
      (try omega) <;>
      (try contradiction) <;>
      (try simp_all [Nat.mul_mod, Nat.add_mod, Nat.mod_mod]) <;>
      (try omega)
    <;>
    (try
      {
        omega
      })
    <;>
    (try
      {
        simp_all [Nat.mul_mod, Nat.add_mod, Nat.mod_mod]
        <;> omega
      })
    <;>
    (try
      {
        ring_nf at *
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
  
  exact h_final
