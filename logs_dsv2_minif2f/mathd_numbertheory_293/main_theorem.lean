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
theorem mathd_numbertheory_293 (n : ℕ) (h₀ : n ≤ 9) (h₁ : 11 ∣ 20 * 100 + 10 * n + 7) : n = 5 := by
    have h_main : n = 5 := by
        have h₂ : n ≤ 9  := by
      
            gcongr
        interval_cases n <;> norm_num [Nat.dvd_iff_mod_eq_zero] at h₁ ⊢ <;> omega
    exact h_main