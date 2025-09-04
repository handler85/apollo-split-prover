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
theorem mathd_algebra_137 (x : ℕ) (h₀ : ↑x + (4 : ℝ) / (100 : ℝ) * ↑x = 598) : x = 575 := by 
    have h1 : ↑x * (1 + (4 : ℝ) / 100) = 598  := by
        linarith
    have h2 : 1 + (4 : ℝ) / 100 = 1.04  := by
        linarith
  
  
    have h5 : 598 / 1.04 = 575  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
        sorry
    exact try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
    sorry