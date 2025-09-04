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

lemma induction_12dvd4expnp1p20_2
  (base_computation : (4 : ℕ) ^ ((0 : ℕ) + (1 : ℕ)) + (20 : ℕ) = (24 : ℕ)) :
  (12 : ℕ) ∣ (24 : ℕ) := by
  have h₁ : (12 : ℕ) ∣ (24 : ℕ) := by
    norm_num [Nat.dvd_iff_mod_eq_zero]
    <;>
    decide
  exact h₁
