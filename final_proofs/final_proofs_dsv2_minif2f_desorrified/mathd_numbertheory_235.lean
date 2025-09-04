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
theorem mathd_numbertheory_235 : (29 * 79 + 31 * 81) % 10 = 2 := by
  have h₁ : (29 * 79 + 31 * 81) % 10 = 2 := by
    norm_num [Nat.mul_mod, Nat.add_mod, Nat.mod_mod]
    <;> rfl
  exact h₁