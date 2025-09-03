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
theorem mathd_algebra_392 (n : ℕ) (h0 : Even n)
    (h1 : (↑n - 2) ^ 2 + ↑n ^ 2 + (↑n + 2) ^ 2 = (12296 : ℤ)) :
    (↑n - 2) * ↑n * (↑n + 2) / 8 = (32736 : ℤ) := by
    have expansion : (↑n - 2)^2 + ↑n^2 + (↑n + 2)^2 = 3 * (↑n)^2 + 8 := by
        linarith
    have eq1 : 3 * (↑n)^2 + 8 = 12296 := by
        linarith
    have eq2 : 3 * (↑n)^2 = 12296 - 8 := by
        linarith
    have eq3 : (↑n)^2 = 4096 := by
        omega
    have eq4 : (↑n) = 64 := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


        
        have h_n_squared : n ^ 2 = 4096 := by
          norm_num [pow_two] at eq3 ⊢
          <;> nlinarith
        
        have h_n : n = 64 := by
          have h2 : n ≤ 100 := by
            by_contra h
            have h3 : n ≥ 101 := by
              by_contra h4
              omega
            have h4 : n ^ 2 > 4096 := by
              have h5 : n ≥ 101 := by omega
              have h6 : n ^ 2 ≥ 101 ^ 2 := by
                exact Nat.pow_le_pow_of_le_left h5 2
              nlinarith
            nlinarith
          interval_cases n <;> norm_num at h_n_squared ⊢ <;> omega
        exact h_n


    have product_calc : (64 - 2) * 64 * (64 + 2) / 8 = 32736 := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith