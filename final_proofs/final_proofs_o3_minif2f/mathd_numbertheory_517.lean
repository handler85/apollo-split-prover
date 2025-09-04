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
theorem mathd_numbertheory_517 : 121 * 122 * 123 % 4 = 2 := by
    have h1 : 121 % 4 = 1 := by
        omega
    have h2 : 122 % 4 = 2 := by
        omega
    have h3 : 123 % 4 = 3 := by
        omega
    have h_mul : (121 * 122 * 123) % 4 = ( (121 % 4) * (122 % 4) * (123 % 4) ) % 4 := by
        gcongr
    have h_subst : (121 * 122 * 123) % 4 = (1 * 2 * 3) % 4 := by
    
        gcongr
    have h_prod : (1 * 2 * 3) % 4 = 6 % 4 := by
        gcongr
    have h_final : 6 % 4 = 2 := by
        gcongr
    rw [h_subst, h_prod, h_final]
  