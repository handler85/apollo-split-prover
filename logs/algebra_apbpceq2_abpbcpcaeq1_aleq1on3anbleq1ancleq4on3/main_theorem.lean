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
theorem algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3 (a b c : ℝ) (h₀ : a ≤ b ∧ b ≤ c)
    (h₁ : a + b + c = 2) (h₂ : a * b + b * c + c * a = 1) :
    0 ≤ a ∧ a ≤ 1 / 3 ∧ 1 / 3 ≤ b ∧ b ≤ 1 ∧ 1 ≤ c ∧ c ≤ 4 / 3 := by
    have bc_expr : b * c = 1 - a * (2 - a)  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
        sorry
    have disc : 4 * a - 3 * a^2 ≥ 0  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
        sorry
    have a_nonneg : 0 ≤ a  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
        sorry
  
  
    have a_bound : a ≤ 1 / 3  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
        sorry
    have b_lower : 1 / 3 ≤ b  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
        sorry
    have b_upper : b ≤ 1  := by
        linarith
    have c_lower : 1 ≤ c  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
        sorry
    have c_upper : c ≤ 4 / 3  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
        sorry
    exact try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
    sorry