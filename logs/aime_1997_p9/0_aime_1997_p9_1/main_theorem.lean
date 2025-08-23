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

lemma aime_1997_p9_1
  (a : ℝ)
  (h₀ : (0 : ℝ) < a)
  (h₁ : Int.fract a⁻¹ = Int.fract (a ^ (2 : ℕ)))
  (h₂ : (2 : ℝ) < a ^ (2 : ℕ))
  (h₃ : a ^ (2 : ℕ) < (3 : ℝ)) :
  ⌊a ^ (2 : ℕ)⌋ = (2 : ℤ) := by
  have h_floor : ⌊a ^ (2 : ℕ)⌋ = 2 := by
    have h₄ : ⌊a ^ (2 : ℕ)⌋ = 2 := by
      rw [Int.floor_eq_iff]
      constructor <;> norm_num at * <;>
      (try norm_num) <;>
      (try nlinarith) <;>
      (try
        {
          constructor <;>
          (try nlinarith) <;>
          (try nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
            Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)])
        }) <;>
      (try
        {
          nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
            Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
            sq_nonneg (a - Real.sqrt 2), sq_nonneg (a - Real.sqrt 3)]
        })
      <;>
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
        Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
        sq_nonneg (a - Real.sqrt 2), sq_nonneg (a - Real.sqrt 3)]
    exact h₄
  exact h_floor
