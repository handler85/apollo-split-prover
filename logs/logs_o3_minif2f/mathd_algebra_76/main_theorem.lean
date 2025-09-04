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
theorem mathd_algebra_76 (f : ℤ → ℤ)
    (h₀ : ∀ n, Odd n → f n = n ^ 2)
    (h₁ : ∀ n, Even n → f n = n ^ 2 - 4 * n - 1) : f 4 = -1 := by 
    have ev4 : Even 4 := by
        decide
    have f4_def : f 4 = 4^2 - 4 * 4 - 1 := by
    
    
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
        sorry
    have four_squared : 4^2 = 16 := by
        linarith
    have four_mul : 4 * 4 = 16 := by
        linarith
    have simplification : 4^2 - 4 * 4 - 1 = 16 - 16 - 1 := by
        rw [four_squared, four_mul]
    
    have final_simplification : 16 - 16 - 1 = -1 := by
        linarith
  
    exact f4_def