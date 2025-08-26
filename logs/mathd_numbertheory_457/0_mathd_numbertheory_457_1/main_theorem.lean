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

lemma mathd_numbertheory_457_1
  (n : ℕ)
  (h₀ : (0 : ℕ) < n)
  (h₁ : (80325 : ℕ) ∣ n !) :
  (17 : ℕ) ≤ n := by
  have h_main : 17 ≤ n := by
    by_contra! h
    have h₂ : n ≤ 16 := by omega
    interval_cases n <;> norm_num [Nat.factorial_succ, Nat.dvd_iff_mod_eq_zero] at h₁ ⊢ <;>
      (try omega) <;>
      (try contradiction) <;>
      (try norm_num at h₁ ⊢) <;>
      (try
        {
          omega
        }) <;>
      (try
        {
          simp_all [Nat.factorial]
          <;> norm_num at *
          <;> omega
        }) <;>
      (try
        {
          norm_num at h₁ ⊢
          <;>
          contradiction
        })
  exact h_main
