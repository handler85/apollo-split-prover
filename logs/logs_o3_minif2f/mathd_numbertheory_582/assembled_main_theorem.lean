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
theorem mathd_numbertheory_582 (n : ℕ) (h₀ : 0 < n) (h₁ : 3 ∣ n) :
    (n + 4 + (n + 6) + (n + 8)) % 9 = 0 := by 
    have h_sum : (n + 4) + (n + 6) + (n + 8) = 3 * n + 18  := by
        linarith
    have h_factor : 3 * n + 18 = 3 * (n + 6)  := by
        linarith
    rcases h₁ with ⟨k, hk⟩
    have h_n : n = 3 * k  := by
        gcongr -- This re-establishes n = 3*k.
    have h_n_plus : n + 6 = 3 * (k + 2)  := by
        linarith
    have h_final : 3 * (n + 6) = 9 * (k + 2)  := by
        linarith
    rw [h_sum, h_factor, h_final]
    omega