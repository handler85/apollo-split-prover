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
theorem algebra_absxm1pabsxpabsxp1eqxp2_0leqxleq1 (x : ℝ)
    (h₀ : abs (x - 1) + abs x + abs (x + 1) = x + 2) : 0 ≤ x ∧ x ≤ 1 := by
  have h_main : 0 ≤ x ∧ x ≤ 1 := by
    constructor
    · -- Prove 0 ≤ x
      by_contra h
      have h₁ : x < 0  := by
        linarith
      cases' le_total 0 (x - 1) with h₂ h₂ <;>
        cases' le_total 0 (x + 1) with h₃ h₃ <;>
        cases' le_total 0 x with h₄ h₄ <;>
        simp_all [abs_of_nonneg, abs_of_nonpos, abs_of_neg, le_of_lt] <;>
        (try { nlinarith }) <;>
        (try {
          cases' le_total 0 (x - 1) with h₅ h₅ <;>
          cases' le_total 0 (x + 1) with h₆ h₆ <;>
          simp_all [abs_of_nonneg, abs_of_nonpos, abs_of_neg, le_of_lt] <;>
          nlinarith
        }) <;>
        (try {
          cases' le_total 0 (x - 1) with h₅ h₅ <;>
          cases' le_total 0 (x + 1) with h₆ h₆ <;>
          simp_all [abs_of_nonneg, abs_of_nonpos, abs_of_neg, le_of_lt] <;>
          nlinarith
        })
    · -- Prove x ≤ 1
      by_contra h
      have h₁ : x > 1  := by
        linarith
      cases' le_total 0 (x - 1) with h₂ h₂ <;>
        cases' le_total 0 (x + 1) with h₃ h₃ <;>
        cases' le_total 0 x with h₄ h₄ <;>
        simp_all [abs_of_nonneg, abs_of_nonpos, abs_of_neg, le_of_lt] <;>
        (try { nlinarith }) <;>
        (try {
          cases' le_total 0 (x - 1) with h₅ h₅ <;>
          cases' le_total 0 (x + 1) with h₆ h₆ <;>
          simp_all [abs_of_nonneg, abs_of_nonpos, abs_of_neg, le_of_lt] <;>
          nlinarith
        }) <;>
        (try {
          cases' le_total 0 (x - 1) with h₅ h₅ <;>
          cases' le_total 0 (x + 1) with h₆ h₆ <;>
          simp_all [abs_of_nonneg, abs_of_nonpos, abs_of_neg, le_of_lt] <;>
          nlinarith
        })
  exact h_main