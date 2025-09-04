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
theorem induction_1pxpownlt1pnx (x : ℝ) (n : ℕ) (h₀ : -1 < x) (h₁ : 0 < n) :
    1 + ↑n * x ≤ (1 + x) ^ (n : ℕ) := by
  try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


  
  have h_main : (1 : ℝ) + (↑n : ℝ) * x ≤ ((1 : ℝ) + x) ^ n := by
    have h₂ : ∀ n : ℕ, n ≠ 0 → (1 : ℝ) + (↑n : ℝ) * x ≤ ((1 : ℝ) + x) ^ n := by
      intro n hn
      induction' n with n ih
      · -- n = 0, but hn : n ≠ 0, so this case is impossible
        exfalso
        exact hn rfl
      · -- n = n + 1
        cases n with
        | zero =>
          -- n = 1
          norm_num
          <;> nlinarith
        | succ n =>
          -- n = n + 1
          simp_all [pow_succ]
          <;>
          (try norm_num) <;>
          (try nlinarith [sq_nonneg x, sq_nonneg (x + 1), sq_nonneg (x - 1)]) <;>
          (try
            {
              nlinarith [sq_nonneg x, sq_nonneg (x + 1), sq_nonneg (x - 1),
                mul_self_nonneg (x ^ 2), mul_self_nonneg (x ^ 2 + x),
                mul_self_nonneg (x ^ 2 - x)]
            }) <;>
          (try
            {
              nlinarith [sq_nonneg x, sq_nonneg (x + 1), sq_nonneg (x - 1),
                mul_self_nonneg (x ^ 2), mul_self_nonneg (x ^ 2 + x),
                mul_self_nonneg (x ^ 2 - x), pow_two_nonneg (x + 1),
                pow_two_nonneg (x - 1)]
            })
    -- Use the result from h₂ to conclude the proof
    have h₃ : n ≠ 0 := by
      intro h
      simp_all
    exact h₂ n h₃
  exact h_main


