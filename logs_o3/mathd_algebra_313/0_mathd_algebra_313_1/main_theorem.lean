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
lemma mathd_algebra_313_1
    (v i z : ℂ)
    (h₂ : z = (2 : ℂ) - Complex.I)
    (h_sub : (1 : ℂ) + Complex.I = i * (2 : ℂ) - i * Complex.I)
    (h₁ : v = i * (2 : ℂ) - i * Complex.I) :
    i = -(i * Complex.I * ((2 : ℂ) - Complex.I)⁻¹) + i * ((2 : ℂ) - Complex.I)⁻¹ * (2 : ℂ) := by
  try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
  try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
  sorry