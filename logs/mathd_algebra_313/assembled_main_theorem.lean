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
theorem mathd_algebra_313 (v i z : ℂ) (h₀ : v = i * z) (h₁ : v = 1 + Complex.I)
    (h₂ : z = 2 - Complex.I) : i = 1 / 5 + 3 / 5 * Complex.I := by
    have h_main : i = 1 / 5 + 3 / 5 * Complex.I := by
        have h₃ : v = i * z  := by
      
            gcongr
        have h₄ : v = 1 + Complex.I  := by
      
            gcongr
        have h₅ : z = 2 - Complex.I  := by
      
            gcongr
        rw [h₄] at h₃
        rw [h₅] at h₃
        have h₆ : (1 + Complex.I : ℂ) = i * (2 - Complex.I)  := by
            simpa using h₃
        have h₇ : i = 1 / 5 + 3 / 5 * Complex.I := by
            have h₈ : i = 1 / 5 + 3 / 5 * Complex.I := by
                have h₉ : (1 + Complex.I : ℂ) = i * (2 - Complex.I)  := by
                    simpa using h₆
                have h₁₀ : i = 1 / 5 + 3 / 5 * Complex.I := by
                    field_simp [Complex.ext_iff, Complex.I_mul_I, mul_comm] at h₉ ⊢
                    constructor <;> ring_nf at h₉ ⊢ <;>
                        (try norm_num at h₉ ⊢) <;>
                        (try nlinarith) <;>
                        (try
                            {
                                nlinarith [sq_nonneg (i.re - 1 / 5), sq_nonneg (i.im - 3 / 5)
                                    sq_nonneg (i.re + 1 / 5), sq_nonneg (i.im + 3 / 5)]
                            }) <;>
                        (try
                            {
                                nlinarith [sq_nonneg (i.re - 1 / 5), sq_nonneg (i.im - 3 / 5)
                                    sq_nonneg (i.re + 1 / 5), sq_nonneg (i.im + 3 / 5)]
                            }) <;>
                        (try
                            {
                                simp_all [Complex.ext_iff, Complex.I_mul_I, mul_comm]
                                <;>
                                ring_nf at * <;>
                                norm_num at * <;>
                                (try constructor <;> nlinarith) <;>
                                (try nlinarith)
                            })
                    <;>
                    (try
                        {
                            nlinarith [sq_nonneg (i.re - 1 / 5), sq_nonneg (i.im - 3 / 5)
                                sq_nonneg (i.re + 1 / 5), sq_nonneg (i.im + 3 / 5)]
                        })
                    <;>
                    (try
                        {
                            nlinarith [sq_nonneg (i.re - 1 / 5), sq_nonneg (i.im - 3 / 5)
                                sq_nonneg (i.re + 1 / 5), sq_nonneg (i.im + 3 / 5)]
                        })
                exact h₁₀
            exact h₈
        exact h₇
    exact h_main