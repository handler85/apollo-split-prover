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
theorem mathd_algebra_139 (s : ℝ → ℝ → ℝ)
    (h₀ : ∀ (x) (_ : x ≠ 0), ∀ (y) (_ : y ≠ 0), s x y = (1 / y - 1 / x) / (x - y)) :
    s 3 11 = 1 / 33 := by
    have h_main : s 3 11 = 1 / 33 := by
        --have h₁ : s 3 11 = (1 / (11 : ℝ) - 1 / (3 : ℝ)) / (3 - 11) := by
            --
            --
            --<;> norm_num at h₂ ⊢ <;> linarith
    
        norm_num
        <;> field_simp
        <;> ring
        <;> norm_num
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
    exact h_main