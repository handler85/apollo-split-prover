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
lemma mathd_algebra_209_1
    (σ : ℝ ≃ ℝ)
    (h₀ : (σ.symm : ℝ → ℝ) (2 : ℝ) = (10 : ℝ))
    (h₁ : (σ.symm : ℝ → ℝ) (10 : ℝ) = (1 : ℝ))
    (h₂ : (σ.symm : ℝ → ℝ) (1 : ℝ) = (2 : ℝ)) :
    (σ : ℝ → ℝ) ((σ : ℝ → ℝ) (10 : ℝ)) = (1 : ℝ) := by
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
        sorry