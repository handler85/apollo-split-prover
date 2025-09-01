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
    (h₁ : b ≤ a)
    (h₂ : (0 : ℝ) < a)
    (h₃ : (0 : ℝ) < b)
    (h₈ : √(a * b) = √a * √b) :
    a * b * (4 : ℝ) - b * √a * √b * (8 : ℝ) + b ^ (2 : ℕ) * (4 : ℝ) ≤ -(a * b * (2 : ℝ)) + a ^ (2 : ℕ) + b ^ (2 : ℕ) := by
    have h_main : a * b * (4 : ℝ) - b * √a * √b * (8 : ℝ) + b ^ (2 : ℕ) * (4 : ℝ) ≤ -(a * b * (2 : ℝ)) + a ^ (2 : ℕ) + b ^ (2 : ℕ) := by
        have h₄ : 0 < a * b := by
            positivity
        have h₅ : 0 < √a := by
            exact sqrt_pos_of_pos h₂
        have h₆ : 0 < √b := by
            exact sqrt_pos_of_pos h₃
        have h₇ : 0 < √a * √b := by
            positivity
        have h₈' : √(a * b) = √a * √b := by
            gcongr
        have h₉ : 0 < √a * √b := by
            positivity
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
        gcongr
    exact h_main