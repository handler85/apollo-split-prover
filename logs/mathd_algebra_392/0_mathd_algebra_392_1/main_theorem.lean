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

lemma mathd_algebra_392_1
  (n : ℕ)
  (h0 : Even n)
  (eq3 : n ^ (2 : ℕ) = (4096 : ℕ))
  (expansion : (4100 : ℕ) + n * (4 : ℕ) + n ^ (2 : ℕ) + (n - (2 : ℕ)) ^ (2 : ℕ) = (12296 : ℕ))
  (h1 : (8 : ℤ) + (↑n : ℤ) ^ (2 : ℕ) * (3 : ℤ) = (12296 : ℤ)) :
  n = (64 : ℕ) := by
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
