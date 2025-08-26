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
lemma algebra_bleqa_apbon2msqrtableqambsqon8b_1
    (a b : ℝ)
    (h₀ : (0 : ℝ) < a ∧ (0 : ℝ) < b)
    (h₁ : b ≤ a) :
    (a + b) / (2 : ℝ) ≤ (a - b) ^ (2 : ℕ) / ((8 : ℝ) * b) + √(a * b) := by
    have h_main : (a + b) / (2 : ℝ) ≤ (a - b) ^ (2 : ℕ) / ((8 : ℝ) * b) + √(a * b) := by
        have h₂ : 0 < a := by
            linarith
        have h₃ : 0 < b := by
            linarith
        have h₄ : 0 < a * b := by
            positivity
        have h₅ : 0 < Real.sqrt (a * b) := by
            exact sqrt_pos_of_pos h₄
        have h₆ : 0 < (8 : ℝ) * b := by
            positivity
        have h₇ : (a - b) ^ (2 : ℕ) / ((8 : ℝ) * b) ≥ (a + b) / (2 : ℝ) - √(a * b) := by
            have h₇₁ : 0 < (8 : ℝ) * b := by
                positivity
            field_simp [h₇₁.ne']
            rw [div_le_div_iff (by positivity) (by positivity)]
            try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
            gcongr
        linarith
    exact h_main