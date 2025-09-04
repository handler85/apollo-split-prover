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
theorem mathd_numbertheory_353 (s : ℕ) (h₀ : s = ∑ k in Finset.Icc 2010 4018, k) : s % 2009 = 0 := by
    have h_sum : s = 2009 * 3014 := by
        rw [h₀]
    
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
        

    have h_main : s % 2009 = 0 := by
        rw [h_sum]
        <;> simp [Nat.mul_mod, Nat.add_mod, Nat.mod_eq_of_lt]
        <;> norm_num
        <;> rfl
    exact h_main