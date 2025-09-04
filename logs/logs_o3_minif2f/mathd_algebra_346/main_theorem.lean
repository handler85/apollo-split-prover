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
theorem mathd_algebra_346 (f g : ℝ → ℝ) (h₀ : ∀ x, f x = 2 * x - 3) (h₁ : ∀ x, g x = x + 1) :
    g (f 5 - 1) = 7 := by
    have h_f5 : f 5 = 2 * 5 - 3  := by
    
        exact h₀ (5 : ℝ)
    have h_mult : 2 * 5 = 10  := by
        linarith
    have h_sub : 10 - 3 = 7  := by
        linarith
    have h_f5_simplified : f 5 = 7  := by
        linarith
    have h_diff : f 5 - 1 = 7 - 1  := by
        linarith
    have h_diff_simplified : 7 - 1 = 6  := by
        linarith
    have h_expr : f 5 - 1 = 6  := by
        linarith
    have h_g_def : g (f 5 - 1) = (f 5 - 1) + 1  := by
    
        exact h₁ (f (5 : ℝ) - (1 : ℝ))
    have h_g_subst : (f 5 - 1) + 1 = 6 + 1  := by
        linarith
    have h_g_simplified : 6 + 1 = 7  := by
        gcongr
    exact try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
    sorry