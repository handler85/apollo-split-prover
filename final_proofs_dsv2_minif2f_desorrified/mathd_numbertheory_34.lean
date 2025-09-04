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
theorem mathd_numbertheory_34 (x : ℕ) (h₀ : x < 100) (h₁ : x * 9 % 100 = 1) : x = 89 := by
  have h_main : x = 89 := by
    have h₂ : x ≤ 99  := by
      linarith
    interval_cases x <;> norm_num at h₁ ⊢ <;>
    (try omega) <;>
    (try contradiction) <;>
    (try
      {
        omega
      }) <;>
    (try
      {
        ring_nf at h₁ ⊢
        omega
      })
    <;>
    (try
      {
        omega
      })
    <;>
    (try
      {
        ring_nf at h₁ ⊢
        omega
      })
  exact h_main