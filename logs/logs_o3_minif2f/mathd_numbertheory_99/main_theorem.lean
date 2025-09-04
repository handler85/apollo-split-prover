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
theorem mathd_numbertheory_99 (n : ℕ) (h₀ : 2 * n % 47 = 15) : n % 47 = 31 := by
    have inv_two : (2 * 24) % 47 = 1  := by
        omega
    have h_mult : (24 * (2 * n)) % 47 = (24 * 15) % 47  := by
        omega
    have h_assoc : ((2 * 24) * n) % 47 = (360) % 47  := by
        omega
    have h_replace : (1 * n) % 47 = 360 % 47  := by
        omega
    have h_calc : 360 % 47 = 31  := by
        omega
    omega