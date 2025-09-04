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
theorem algebra_absapbon1pabsapbleqsumabsa (a b : ℝ) :
    abs (a + b) / (1 + abs (a + b)) ≤ abs a / (1 + abs a) + abs b / (1 + abs b) := by
    have h_tri : abs (a + b) ≤ abs a + abs b := by
        exact abs_add_le a b
    have f_mono : ∀ {x y : ℝ}, 0 ≤ x → 0 ≤ y → x ≤ y → x/(1+x) ≤ y/(1+y) := by
        intros; gcongr
    have mono_apply : (abs (a + b))/(1 + abs (a + b)) ≤ (abs a + abs b)/(1 + abs a + abs b) := by
        gcongr
    have aux_ineq : ∀ (u v : ℝ), 0 ≤ u → 0 ≤ v → (u + v)/(1 + u + v) ≤ u/(1 + u) + v/(1 + v) := by
        intros; try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
        

    have final_step : (abs a + abs b)/(1 + abs a + abs b) ≤ abs a/(1 + abs a) + abs b/(1 + abs b) := by
        apply aux_ineq; 
    
        exact abs_nonneg b
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
        

    exact le_trans mono_apply final_step