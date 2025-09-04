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
theorem mathd_numbertheory_764 (p : ℕ) (h₀ : Nat.Prime p) (h₁ : 7 ≤ p) :
    (∑ k in Finset.Icc 1 (p - 2), (k : ZMod p)⁻¹ * ((k : ZMod p) + 1)⁻¹) = 2 := by
    have h_partial_fraction : ∀ k ∈ Finset.Icc 1 (p - 2), ((k : ZMod p) * ((k : ZMod p) + 1))⁻¹ = (k : ZMod p)⁻¹ - ((k : ZMod p) + 1)⁻¹ := by
        intros k hk
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
        sorry
    have h_inv1 : (1 : ZMod p)⁻¹ = 1 := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
    exact ZMod.inv_one p