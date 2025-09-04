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
theorem mathd_numbertheory_320 (n : ℕ) (h₀ : n < 101) (h₁ : 101 ∣ 123456 - n) : n = 34 := by
  have step1 : 123456 = 101 * 1222 + 34  := by
      linarith
  have step2 : ∃ k, 123456 - n = 101 * k  := by
      exact h₁
  have step3 : 123456 % 101 = 34  := by
      omega
  have step4 : n = 34  := by
      omega
  exact step4