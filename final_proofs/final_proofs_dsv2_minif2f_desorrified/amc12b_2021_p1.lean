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
theorem amc12b_2021_p1 (S : Finset ℤ) (h₀ : ∀ x : ℤ, x ∈ S ↔ ↑(abs x) < 3 * Real.pi) :
    S.card = 19 := by
  try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


  
  have h₁ : S = { -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9 } := by
      apply Finset.ext
      intro x
      simp only [Finset.mem_insert, Finset.mem_singleton, h₀]
      constructor
      try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
      intro
      try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
      intro
  have h₂ : S.card = 19 := by
      rw [h₁]
      rfl
  rw [h₂]
  <;> norm_num
  <;>
  aesop

