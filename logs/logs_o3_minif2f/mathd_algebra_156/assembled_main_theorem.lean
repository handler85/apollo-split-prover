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
theorem mathd_algebra_156 (x y : ℝ) (f g : ℝ → ℝ)
    (h₀ : ∀ t, f t = t ^ 4)
    (h₁ : ∀ t, g t = 5 * t ^ 2 - 6)
    (h₂ : f x = g x)
    (h₃ : f y = g y)
    (h₄ : x ^ 2 < y ^ 2) : 
    y ^ 2 - x ^ 2 = 1 := by
    --{ rw [h₀, h₁]
        --
    --{ rw [h₀, h₁]
    
    --{ rw [hx_eq]
        --ring, }
    --{ rw [hy_eq]
        --ring, }
  
    exact try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
    sorry
