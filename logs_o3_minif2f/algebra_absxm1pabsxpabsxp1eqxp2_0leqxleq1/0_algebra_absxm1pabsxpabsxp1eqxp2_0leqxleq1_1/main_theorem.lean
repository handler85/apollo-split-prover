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

lemma algebra_absxm1pabsxpabsxp1eqxp2_0leqxleq1_1
  (x : ℝ)
  (h₀ : |x - (1 : ℝ)| + |x| + |x + (1 : ℝ)| = x + (2 : ℝ)) :
  (0 : ℝ) ≤ x := by
  have h_main : 0 ≤ x := by
    by_contra h
    have h₁ : x < 0 := by linarith
    have h₂ : |x - 1| + |x| + |x + 1| = x + 2 := by linarith
    cases' le_or_lt 0 (x - 1) with h₃ h₃ <;>
    cases' le_or_lt 0 (x + 1) with h₄ h₄ <;>
    cases' le_or_lt 0 x with h₅ h₅ <;>
    simp_all [abs_of_nonneg, abs_of_neg, abs_of_nonpos, abs_of_pos, sub_nonneg, sub_nonpos] <;>
    (try { contradiction }) <;>
    (try { linarith }) <;>
    (try {
      nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1), sq_nonneg x]
    }) <;>
    (try {
      cases' le_total 0 (x - 1) with h₆ h₆ <;>
      cases' le_total 0 (x + 1) with h₇ h₇ <;>
      cases' le_total 0 x with h₈ h₈ <;>
      simp_all [abs_of_nonneg, abs_of_neg, abs_of_nonpos, abs_of_pos, sub_nonneg, sub_nonpos] <;>
      nlinarith
    })
  exact h_main
