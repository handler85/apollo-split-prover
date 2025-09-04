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
theorem mathd_numbertheory_345 : (2000 + 2001 + 2002 + 2003 + 2004 + 2005 + 2006) % 7 = 0 := by
    have sum_expr : 2000 + 2001 + 2002 + 2003 + 2004 + 2005 + 2006 = 7 * 2003 := by
        linarith
    have mod_property : (7 * 2003) % 7 = 0 := by
        omega
    rw [sum_expr, mod_property]
  