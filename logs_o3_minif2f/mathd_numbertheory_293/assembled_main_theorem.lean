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
theorem mathd_numbertheory_293 (n : ℕ) (h₀ : n ≤ 9) (h₁ : 11 ∣ (20 * 100 + 10 * n + 7)) : n = 5 := by
  have h_expr : 20 * 100 + 10 * n + 7 = 2007 + 10 * n  := by
      linarith
  have h_div : 11 ∣ (2007 + 10 * n)  := by
      omega
  have h_2007 : 2007 % 11 = 5  := by
      omega
  have h_mod : (2007 + 10 * n) % 11 = 0  := by
      omega
  have h_equiv : (5 + 10 * n) % 11 = 0  := by
      omega
  have h_congruence : (10 * n) % 11 = 6  := by
      omega
  have h_mul : (10 * (10 * n)) % 11 = (10 * 6) % 11  := by
    omega
  have h_n_mod : n % 11 = 60 % 11  := by
      omega
  have h_simpl : 60 % 11 = 5  := by
      gcongr
  have h_final : n = 5  := by
      omega
  exact h_final