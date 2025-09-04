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
theorem mathd_algebra_452 (a : ℕ → ℝ) (h₀ : ∀ n, a (n + 2) - a (n + 1) = a (n + 1) - a n)
    (h₁ : a 1 = 2 / 3) (h₂ : a 9 = 4 / 5) : a 5 = 11 / 15 := by
    have h_common_diff : a 2 - a 1 = 1 / 60 := by
    
    
    
    
    
    
    
    
    
    
        norm_num at *
    
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
        sorry
    have h_a5 : a 5 = 11 / 15 := by
    
    
    
    
    
    
    
    
    
    
        norm_num at *
    
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
        sorry
    exact h_a5