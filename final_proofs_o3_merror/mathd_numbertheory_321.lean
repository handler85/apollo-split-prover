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
theorem mathd_numbertheory_321 (n : ZMod 1399) (h₁ : n = 160⁻¹) : n = 1058 := by
    have step1 : 160 * 1058 = 169280 := by
        linarith
    have step2 : 1399 * 121 = 169279 := by
        linarith
    have step3 : 160 * 1058 = 1399 * 121 + 1 := by
        gcongr
    have step4 : (160 * 1058 : ℤ) ≡ 1 [ZMOD 1399] := by
        decide
    have step5 : 160⁻¹ = (1058 : ZMod 1399) := by
        exact ZMod.inv_eq_of_mul_eq_one (1399 : ℕ) (160 : ZMod (1399 : ℕ)) (1058 : ZMod (1399 : ℕ)) rfl
    rw [h₁, step5]
  