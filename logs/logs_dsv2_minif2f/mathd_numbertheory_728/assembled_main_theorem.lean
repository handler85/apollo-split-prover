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
theorem mathd_numbertheory_728 : (29 ^ 13 - 5 ^ 13) % 7 = 3 := by
    have h_main : (29 ^ 13 - 5 ^ 13) % 7 = 3 := by
        --norm_num [Nat.pow_mod, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt
            --
            --
            --
        --<;> rfl
        omega
    exact h_main