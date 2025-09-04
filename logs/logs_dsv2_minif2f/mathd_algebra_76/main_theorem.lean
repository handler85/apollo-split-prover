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
theorem mathd_algebra_76 (f : ℤ → ℤ) (h₀ : ∀ n, Odd n → f n = n ^ 2)
    (h₁ : ∀ n, Even n → f n = n ^ 2 - 4 * n - 1) : f 4 = -1 := by
  have h_f4 : f 4 = -1 := by
    have h₂ : Even (4 : ℤ) := by
      exact even_iff_two_dvd.mpr (by norm_num)
    have h₃ : f 4 = 4 ^ 2 - 4 * 4 - 1 := by
      rw [h₁ 4 h₂]
      <;> norm_num
    rw [h₃]
    <;> norm_num
    <;> rfl
  exact h_f4