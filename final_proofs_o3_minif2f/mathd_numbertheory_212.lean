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
theorem mathd_numbertheory_212 : 16 ^ 17 * 17 ^ 18 * 18 ^ 19 % 10 = 8 := by
    have h1 : 16 % 10 = 6  := by
        omega
    have h2 : 17 % 10 = 7  := by
        omega
    have h3 : 18 % 10 = 8  := by
        omega
    have h16 : (16 ^ 17) % 10 = (6 ^ 17) % 10  := by
        omega
    have h17 : (17 ^ 18) % 10 = (7 ^ 18) % 10  := by
        omega
    have h18 : (18 ^ 19) % 10 = (8 ^ 19) % 10  := by
        omega
    have h6 : (6 ^ 17) % 10 = 6  := by
        omega
    have h7 : (7 ^ 18) % 10 = 9  := by
        omega
    have h8 : (8 ^ 19) % 10 = 2  := by
        omega
    have hprod : ((6 ^ 17) * (7 ^ 18) * (8 ^ 19)) % 10 = (6 * 9 * 2) % 10  := by
        omega
    have hcalc : (6 * 9 * 2) % 10 = 8  := by
        gcongr
    have h_final : (16 ^ 17 * 17 ^ 18 * 18 ^ 19) % 10 = ((6 ^ 17) * (7 ^ 18) * (8 ^ 19)) % 10  := by
        omega
    rw [h_final, h6, h7, h8, hprod, hcalc] at *
  