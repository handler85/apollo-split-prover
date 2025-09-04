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
theorem mathd_numbertheory_185 (n : ℕ) (h₀ : n % 5 = 3) : 2 * n % 5 = 1 := by
    have h_main : 2 * n % 5 = 1 := by
        have h₁ : n % 5 = 3  := by
      
            gcongr
        have h₂ : 2 * n % 5 = 1 := by
            rw [← Nat.mod_add_div n 5]
            simp [h₁, Nat.mul_mod, Nat.add_mod, Nat.mod_mod, Nat.mul_mod, Nat.add_mod, Nat.mod_mod]
            <;> norm_num <;> omega
        exact h₂
    exact h_main