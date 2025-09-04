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
theorem amc12b_2020_p2 :
    (100 ^ 2 - 7 ^ 2 : ℝ) / (70 ^ 2 - 11 ^ 2) * ((70 - 11) * (70 + 11) / ((100 - 7) * (100 + 7))) = 1 := by 
    have h1 : 100^2 - 7^2 = (100 - 7) * (100 + 7)  := by
        omega
    have h2 : 70^2 - 11^2 = (70 - 11) * (70 + 11)  := by
        omega
    have h3 : (100 ^ 2 - 7 ^ 2) / (70 ^ 2 - 11 ^ 2) * ((70 - 11) * (70 + 11) / ((100 - 7) * (100 + 7))) = ((100 - 7) * (100 + 7)) / ((70 - 11) * (70 + 11)) * ((70 - 11) * (70 + 11) / ((100 - 7) * (100 + 7)))  := by
        omega
    have h4 : ((100 - 7) * (100 + 7)) / ((70 - 11) * (70 + 11)) * ((70 - 11) * (70 + 11) / ((100 - 7) * (100 + 7))) = 1  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
        sorry

    linarith