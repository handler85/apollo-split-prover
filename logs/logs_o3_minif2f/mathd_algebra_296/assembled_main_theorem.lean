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
theorem mathd_algebra_296 : abs ((3491 - 60) * (3491 + 60) - 3491 ^ 2 : ℤ) = 3600 := by 
    have diff_sq : (3491 - 60) * (3491 + 60) = 3491 ^ 2 - 60 ^ 2 := by
        omega
    have expr_eq : (3491 - 60) * (3491 + 60) - 3491 ^ 2 = - 60 ^ 2 := by
        linarith
    have abs_eq : abs (- 60 ^ 2) = 60 ^ 2 := by
        decide
    have square_val : 60 ^ 2 = 3600 := by
        linarith
    decide