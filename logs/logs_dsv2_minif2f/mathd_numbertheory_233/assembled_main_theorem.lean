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
theorem mathd_numbertheory_233 (b : ZMod (11 ^ 2)) (h₀ : b = 24⁻¹) : b = 116 := by
    have h₁ : b = 116 := by
        rw [h₀]
        apply Eq.symm
    
        exact Eq.symm (ZMod.inv_eq_of_mul_eq_one ((11 : ℕ) ^ (2 : ℕ)) (24 : ZMod ((11 : ℕ) ^ (2 : ℕ))) (116 : ZMod ((11 : ℕ) ^ (2 : ℕ))) rfl)
    exact h₁