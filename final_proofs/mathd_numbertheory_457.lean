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
theorem mathd_numbertheory_457 (n : ℕ) (h₀ : 0 < n) (h₁ : 80325 ∣ n !) : 17 ≤ n := by
    have h_factor : 80325 = 3^3 * 5^2 * 7 * 17 := by
        linarith
  
    have h_n_ge_17 : 17 ≤ n := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


        
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


    exact h_n_ge_17