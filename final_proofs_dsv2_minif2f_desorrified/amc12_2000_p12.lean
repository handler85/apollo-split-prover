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
theorem amc12_2000_p12 (a m c : ℕ) (h₀ : a + m + c = 12) :
    a * m * c + a * m + m * c + a * c ≤ 112 := by
  have h_main : a * m * c + a * m + m * c + a * c ≤ 112 := by
    have h₁ : a ≤ 12  := by
      omega
    have h₂ : m ≤ 12  := by
      omega
    have h₃ : c ≤ 12  := by
      omega
    interval_cases a <;> interval_cases m <;> interval_cases c <;> norm_num at h₀ ⊢ <;>
      (try omega) <;> (try nlinarith) <;> (try ring_nf at h₀ ⊢) <;> (try omega)
    <;>
    (try
      {
        nlinarith
      })
    <;>
    (try
      {
        ring_nf at h₀ ⊢
        omega
      })
    <;>
    (try
      {
        nlinarith
      })
    <;>
    (try
      {
        ring_nf at h₀ ⊢
        omega
      })
  exact h_main