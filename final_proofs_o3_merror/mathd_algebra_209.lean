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
theorem mathd_algebra_209 (σ : Equiv ℝ ℝ)
    (h₀ : σ.2 2 = 10) (h₁ : σ.2 10 = 1) (h₂ : σ.2 1 = 2) : σ.1 (σ.1 10) = 1 := by
  try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


  
  (try norm_num at * <;> linarith) <;>
  (try nlinarith) <;>
  (try
      {
          nlinarith [sq_nonneg (σ.symm 2 - σ.symm 1), sq_nonneg (σ.symm 1 - σ.symm 10), sq_nonneg (σ.symm 10 - σ.symm 2)]
      }) <;>
  (try
      {
          aesop
      }) <;>
  (try
      {
          simp_all [Equiv.eq_symm_apply]
          <;> nlinarith
      })
  <;>
  (try
      {
          aesop
      })
  <;>
  (try
      {
          nlinarith
      })
  try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
  try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


  
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


