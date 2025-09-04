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
theorem induction_12dvd4expnp1p20 (n : ℕ) : 12 ∣ 4^(n + 1) + 20 := by
    induction n with
        | zero =>
            have base_computation : 4^(0 + 1) + 20 = 24  := by
                sorry
            have base_divisible : 12 ∣ 24  := by
                sorry
            exact base_divisible
        | succ n ih =>
      
            have step1 : 4^(n + 2) + 20 = 4 * (4^(n + 1) + 20) - 60  := by
                sorry
      
      
      
            sorry