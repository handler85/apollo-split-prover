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
theorem induction_11div10tonmn1ton (n : ℕ) : 11 ∣ 10 ^ n - (-1 : ℤ) ^ n := by
    induction n with
        | zero =>
            have base : 10^0 - (-1 : ℤ)^0 = 0 := by
                linarith
            exact dvd_zero 11
        | succ n ih =>
            have step1 : 10^(n+1) - (-1)^(n+1) = 10 * (10^n - (-1)^n) + (-1)^n * (10 - (-1)) := by
                omega
            have factor1 : 11 ∣ 10 * (10^n - (-1)^n) := by
                omega
            have factor2 : 11 ∣ (-1)^n * (10 - (-1)) := by
                omega
            have conclusion : 11 ∣ (10 * (10^n - (-1)^n) + (-1)^n * (10 - (-1))) := by
                omega
      
            omega