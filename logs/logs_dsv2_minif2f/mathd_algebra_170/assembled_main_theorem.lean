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
theorem mathd_algebra_170 (S : Finset ℤ) (h₀ : ∀ n : ℤ, n ∈ S ↔ abs (n - 2) ≤ 5 + 6 / 10) :
    S.card = 11 := by
  have h₁ : S = { -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7 } := by
    apply Finset.ext
    intro n
    simp only [Finset.mem_insert, Finset.mem_singleton, h₀]
    constructor
    · -- Prove the forward direction: if n satisfies the inequality, then n is in the set { -3, -2, ..., 7 }
      intro h
      have h₁ : abs (n - 2) ≤ 5 + 6 / 10  := by
        simpa using h
      have h₂ : abs (n - 2) ≤ 28 / 5 := by
        norm_num at h₁ ⊢
        <;>
        (try omega) <;>
        (try
          {
            norm_num [abs_le] at h₁ ⊢ <;>
            (try omega) <;>
            (try
              {
                constructor <;>
                (try omega) <;>
                (try
                  {
                    linarith
                  })
              })
          }) <;>
        (try
          {
            rcases le_total 0 (n - 2) with h₃ | h₃ <;>
            rcases le_total 0 (n - 2) with h₄ | h₄ <;>
            simp_all [abs_of_nonneg, abs_of_nonpos, abs_le] <;>
            (try omega) <;>
            (try
              {
                norm_num at * <;>
                (try omega) <;>
                (try
                  {
                    omega
                  })
              })
          })
        <;>
        (try
          {
            norm_num at * <;>
            (try omega) <;>
            (try
              {
                omega
              })
          })
        <;>
        (try
          {
            norm_num [abs_le] at h₁ ⊢ <;>
            omega
          })
        <;>
        (try
          {
            norm_num [abs_le] at h₁ ⊢ <;>
            omega
          })
      have h₃ : n ≥ -3 := by
        by_contra h₄
        have h₅ : n ≤ -4  := by
          omega
        have h₆ : abs (n - 2) > 28 / 5 := by
          have h₇ : n ≤ -4  := by
            omega
          have h₈ : abs (n - 2) ≥ 6 := by
            cases' abs_cases (n - 2) with h₉ h₉ <;>
            omega
          norm_num at h₈ ⊢ <;>
          omega
        omega
      have h₄ : n ≤ 7 := by
        by_contra h₅
        have h₆ : n ≥ 8  := by
          omega
        have h₇ : abs (n - 2) > 28 / 5 := by
          have h₈ : n ≥ 8  := by
            omega
          have h₉ : abs (n - 2) ≥ 6 := by
            cases' abs_cases (n - 2) with h₁₀ h₁₀ <;>
            omega
          norm_num at h₉ ⊢ <;>
          omega
        omega
      interval_cases n <;> norm_num [abs_le] at h₂ ⊢ <;>
      (try omega) <;>
      (try
        {
          norm_num at h₂ ⊢ <;>
          (try omega) <;>
          (try
            {
              aesop
            })
        }) <;>
      (try
        {
          aesop
        })
    · -- Prove the reverse direction: if n is in the set { -3, -2, ..., 7 }, then it satisfies the inequality
      intro h
      rcases h with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      norm_num [abs_le] <;>
      (try omega) <;>
      (try
        {
          norm_num
          <;>
          aesop
        })
      <;>
      (try
        {
          norm_num
          <;>
          aesop
        })
      <;>
      (try
        {
          norm_num
          <;>
          aesop
        })
  have h₂ : S.card = 11 := by
    rw [h₁]
    rfl
  exact h₂