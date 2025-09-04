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
theorem mathd_algebra_209 (σ : Equiv ℝ ℝ) (h₀ : σ.2 2 = 10) (h₁ : σ.2 10 = 1) (h₂ : σ.2 1 = 2) :
    σ.1 (σ.1 10) = 1 := by
    have h₃ : σ.1 1 = 10 := by
        have h₃₁ : σ.1 (σ.2 10) = 10  := by
            simp [Equiv.eq_symm_apply]
        have h₃₂ : σ.2 10 = 1  := by
      
            gcongr
        rw [h₃₂] at h₃₁
        simpa using h₃₁
    have h₄ : σ.1 10 = 2 := by
        have h₄₁ : σ.1 (σ.2 2) = 2  := by
            simp [Equiv.eq_symm_apply]
        have h₄₂ : σ.2 2 = 10  := by
      
            gcongr
        rw [h₄₂] at h₄₁
        simpa using h₄₁
    have h₅ : σ.1 2 = 1 := by
        have h₅₁ : σ.1 (σ.2 1) = 1  := by
            simp [Equiv.eq_symm_apply]
        have h₅₂ : σ.2 1 = 2  := by
      
            gcongr
        rw [h₅₂] at h₅₁
        simpa using h₅₁
    have h₆ : σ.1 (σ.1 10) = 1 := by
        --have h₆₁ : σ.1 10 = 2  := by
            --
            --simp_all only [Equiv.invFun_as_coe, Equiv.toFun_as_coe]
        ----have h₆₂ : σ.1 2 = 1  := by
            ----
            ----
            --
      
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
    exact h₆