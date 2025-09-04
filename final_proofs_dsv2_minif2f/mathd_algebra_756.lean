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
theorem mathd_algebra_756 (a b : ℝ) (h₀ : (2 : ℝ) ^ a = 32) (h₁ : a ^ b = 125) : b ^ a = 243 := by
    have h_a : a = 5 := by
        have h₂ : a = 5 := by
            have h₃ : (2 : ℝ) ^ a = 32  := by
        
                gcongr
            have h₄ : (2 : ℝ) ^ a = (2 : ℝ) ^ (5 : ℝ)  := by
                norm_num at h₃ ⊢ <;> linarith
            have h₅ : a = 5 := by
                apply_fun (fun x => Real.logb 2 x) at h₄
                field_simp [Real.logb_pow, Real.logb_rpow, Real.logb_pow] at h₄ ⊢
                <;> linarith
            exact h₅
        exact h₂
    have h_b : b = 3 := by
        have h₂ : a ^ b = 125  := by
      
            gcongr
        rw [h_a] at h₂
        have h₃ : (5 : ℝ) ^ b = 125  := by
            simpa using h₂
        have h₄ : b = 3 := by
            have h₅ : (5 : ℝ) ^ b = 125  := by
        
                gcongr
            have h₆ : b = 3 := by
                have h₇ : (5 : ℝ) ^ b = (5 : ℝ) ^ (3 : ℝ)  := by
                    norm_num at h₅ ⊢ <;> linarith
                have h₈ : b = 3 := by
                    apply_fun (fun x => Real.logb 5 x) at h₇
                    field_simp [Real.logb_pow, Real.logb_rpow, Real.logb_pow] at h₇ ⊢
                    <;> linarith
                exact h₈
            exact h₆
        exact h₄
    have h_main : b ^ a = 243 := by
        rw [h_b, h_a]
        <;> norm_num
        <;>
        simp_all [Real.rpow_def_of_pos, Real.exp_log]
        <;>
        norm_num
        <;>
        ring_nf
        <;>
        norm_num
        <;>
        linarith
    exact h_main