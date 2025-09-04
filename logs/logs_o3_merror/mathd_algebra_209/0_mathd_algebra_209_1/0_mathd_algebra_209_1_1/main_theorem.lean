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
lemma mathd_algebra_209_1_1
    (σ : ℝ ≃ ℝ)
    (h₀ : (σ.symm : ℝ → ℝ) (2 : ℝ) = (10 : ℝ))
    (h₁ : (σ.symm : ℝ → ℝ) (10 : ℝ) = (1 : ℝ))
    (h₂ : (σ.symm : ℝ → ℝ) (1 : ℝ) = (2 : ℝ)) :
    (σ : ℝ → ℝ) ((σ : ℝ → ℝ) (10 : ℝ)) = (1 : ℝ) := by
    have h₃ : σ 10 = 2 := by
        have h₃₁ : σ.symm 2 = 10  := by
            simpa using h₀
        have h₃₂ : σ.symm 2 = 10  := by
      
            gcongr
        --have h₃₃ : σ 10 = 2 := by
            --
            --<;> aesop
    
        exact (Equiv.apply_eq_iff_eq_symm_apply σ).mpr (id (Eq.symm h₀))
    have h₄ : (σ : ℝ → ℝ) ((σ : ℝ → ℝ) (10 : ℝ)) = 1 := by
        have h₄₁ : (σ : ℝ → ℝ) ((σ : ℝ → ℝ) (10 : ℝ)) = (σ : ℝ → ℝ) (σ 10)  := by
            rfl
        rw [h₄₁]
        have h₄₂ : σ 10 = 2  := by
      
            gcongr
        rw [h₄₂]
        have h₄₃ : (σ : ℝ → ℝ) (2 : ℝ) = 1 := by
            have h₄₄ : (σ.symm : ℝ → ℝ) (1 : ℝ) = (2 : ℝ)  := by
        
                gcongr
            have h₄₅ : (σ : ℝ → ℝ) ((σ.symm : ℝ → ℝ) (1 : ℝ)) = (1 : ℝ) := by
                simp [Equiv.symm_apply_apply]
            rw [h₄₄] at h₄₅
            simpa [Equiv.symm_apply_apply] using h₄₅
        simpa [Equiv.symm_apply_apply] using h₄₃
    exact h₄