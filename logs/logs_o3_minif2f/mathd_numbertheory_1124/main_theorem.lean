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
theorem mathd_numbertheory_1124 (n : ℕ) (h₀ : n ≤ 9) (h₁ : 18 ∣ (374 * 10 + n)) : n = 4 := by 
  let num := 374 * 10 + n
  have h_num: num = 3740 + n  := by
      omega
  have div2: 2 ∣ num  := by
      omega
  have n_even: n % 2 = 0  := by
      omega
  have div9: 9 ∣ num  := by
      omega
  have digit_sum: 3 + 7 + 4 + n = 14 + n  := by
      linarith
  have sum_div9: 9 ∣ (14 + n)  := by
      omega
  have mod_condition: (5 + n) % 9 = 0  := by
      omega
  have final_result: n = 4  := by
      omega
  exact final_result