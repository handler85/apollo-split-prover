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

lemma amc12a_2021_p14_1:
  (∑ k ∈ Finset.Icc (1 : ℕ) (20 : ℕ), logb ((5 : ℝ) ^ k) ((3 : ℝ) ^ k ^ (2 : ℕ))) *
      ∑ k ∈ Finset.Icc (1 : ℕ) (100 : ℕ), logb ((9 : ℝ) ^ k) ((25 : ℝ) ^ k) =
    (21000 : ℝ) := by
  have h_main : (∑ k ∈ Finset.Icc (1 : ℕ) (20 : ℕ), logb ((5 : ℝ) ^ k) ((3 : ℝ) ^ k ^ (2 : ℕ))) * (∑ k ∈ Finset.Icc (1 : ℕ) (100 : ℕ), logb ((9 : ℝ) ^ k) ((25 : ℝ) ^ k)) = (21000 : ℝ) := by
    have h₁ : (∑ k ∈ Finset.Icc (1 : ℕ) (20 : ℕ), logb ((5 : ℝ) ^ k) ((3 : ℝ) ^ k ^ (2 : ℕ))) = (210 : ℝ) * ((Real.log 3) / (Real.log 5)) := by
      have h₂ : ∀ k ∈ Finset.Icc (1 : ℕ) (20 : ℕ), logb ((5 : ℝ) ^ k) ((3 : ℝ) ^ k ^ (2 : ℕ)) = (k * Real.log 3) / (Real.log 5) := by
        intro k hk
        have h₃ : k ∈ Finset.Icc (1 : ℕ) (20 : ℕ) := hk
        have h₄ : 1 ≤ k ∧ k ≤ 20 := by simpa using h₃
        have h₅ : (k : ℕ) ≥ 1 := by linarith
        have h₆ : (k : ℕ) ≤ 20 := by linarith
        have h₇ : logb ((5 : ℝ) ^ k) ((3 : ℝ) ^ k ^ (2 : ℕ)) = (Real.log ((3 : ℝ) ^ (k ^ (2 : ℕ)))) / (Real.log ((5 : ℝ) ^ k)) := by
          simp [logb]
          <;> ring_nf
        rw [h₇]
        have h₈ : Real.log ((3 : ℝ) ^ (k ^ (2 : ℕ))) = (k ^ (2 : ℕ) : ℝ) * Real.log 3 := by
          simp [Real.log_rpow (by norm_num : (3 : ℝ) > 0)]
          <;> ring_nf
        rw [h₈]
        have h₉ : Real.log ((5 : ℝ) ^ k) = (k : ℝ) * Real.log 5 := by
          simp [Real.log_rpow (by norm_num : (5 : ℝ) > 0)]
          <;> ring_nf
        rw [h₉]
        have h₁₀ : ((k ^ (2 : ℕ) : ℝ) * Real.log 3) / ((k : ℝ) * Real.log 5) = (k * Real.log 3) / (Real.log 5) := by
          cases k with
          | zero => norm_num at h₄ <;> simp_all [Nat.div_eq_of_lt] <;> norm_num <;> linarith
          | succ k' =>
            field_simp [Nat.cast_add_one_ne_zero]
            <;> ring_nf
            <;> field_simp [Nat.cast_add_one_ne_zero]
            <;> ring_nf
            <;> simp_all [pow_succ]
            <;> ring_nf
            <;> nlinarith
        rw [h₁₀]
        <;> field_simp
        <;> ring_nf
      calc
        (∑ k ∈ Finset.Icc (1 : ℕ) (20 : ℕ), logb ((5 : ℝ) ^ k) ((3 : ℝ) ^ k ^ (2 : ℕ))) = ∑ k ∈ Finset.Icc (1 : ℕ) (20 : ℕ), ((k * Real.log 3) / (Real.log 5)) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [h₂ k hk]
        _ = (∑ k ∈ Finset.Icc (1 : ℕ) (20 : ℕ), (k * Real.log 3) / (Real.log 5)) := by rfl
        _ = (210 : ℝ) * ((Real.log 3) / (Real.log 5)) := by
          -- Calculate the sum of the series
          norm_num [Finset.sum_Icc_succ_top]
          <;>
            field_simp
            <;>
            ring_nf
            <;>
            norm_num
            <;>
            (try simp_all [Finset.sum_range_succ, logb])
            <;>
            (try field_simp)
            <;>
            (try ring_nf)
            <;>
            (try norm_num)
            <;>
            (try linarith)
            <;>
            (try nlinarith)
            <;>
            (try
              {
                norm_num [logb, Real.logb, Real.log_div, Real.log_mul, Real.log_rpow, Real.log_pow] at *
                <;>
                  ring_nf at *
                <;>
                  nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 3), Real.log_pos (by norm_num : (1 : ℝ) < 5)]
              })
            <;>
            (try
              {
                norm_num [logb, Real.logb, Real.log_div, Real.log_mul, Real.log_rpow, Real.log_pow] at *
                <;>
                  ring_nf at *
                <;>
                  nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 3), Real.log_pos (by norm_num : (1 : ℝ) < 5)]
              })
    have h₂ : (∑ k ∈ Finset.Icc (1 : ℕ) (100 : ℕ), logb ((9 : ℝ) ^ k) ((25 : ℝ) ^ k)) = (100 : ℝ) * ((Real.log 25) / (Real.log 9)) := by
      have h₃ : ∀ k ∈ Finset.Icc (1 : ℕ) (100 : ℕ), logb ((9 : ℝ) ^ k) ((25 : ℝ) ^ k) = (Real.log 25) / (Real.log 9) := by
        intro k hk
        have h₄ : k ∈ Finset.Icc (1 : ℕ) (100 : ℕ) := hk
        have h₅ : 1 ≤ k ∧ k ≤ 100 := by simpa using h₄
        have h₆ : (k : ℕ) ≥ 1 := by linarith
        have h₇ : (k : ℕ) ≤ 100 := by linarith
        have h₈ : logb ((9 : ℝ) ^ k) ((25 : ℝ) ^ k) = (Real.log ((25 : ℝ) ^ k)) / (Real.log ((9 : ℝ) ^ k)) := by
          simp [logb]
          <;> ring_nf
        rw [h₈]
        have h₉ : Real.log ((25 : ℝ) ^ k) = (k : ℝ) * Real.log 25 := by
          simp [Real.log_rpow (by norm_num : (25 : ℝ) > 0)]
          <;> ring_nf
        have h₁₀ : Real.log ((9 : ℝ) ^ k) = (k : ℝ) * Real.log 9 := by
          simp [Real.log_rpow (by norm_num : (9 : ℝ) > 0)]
          <;> ring_nf
        rw [h₉, h₁₀]
        have h₁₁ : ((k : ℝ) * Real.log 25) / ((k : ℝ) * Real.log 9) = (Real.log 25) / (Real.log 9) := by
          have h₁₂ : (k : ℝ) ≠ 0 := by
            norm_cast
            <;> linarith
          field_simp [h₁₂]
          <;> ring_nf
        rw [h₁₁]
        <;> simp [h₅]
        <;> ring_nf
      calc
        (∑ k ∈ Finset.Icc (1 : ℕ) (100 : ℕ), logb ((9 : ℝ) ^ k) ((25 : ℝ) ^ k)) = ∑ k ∈ Finset.Icc (1 : ℕ) (100 : ℕ), ((Real.log 25) / (Real.log 9)) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [h₃ k hk]
        _ = (100 : ℝ) * ((Real.log 25) / (Real.log 9)) := by
          norm_num [Finset.sum_Icc_succ_top]
          <;>
            field_simp
            <;>
            ring_nf
            <;>
            norm_num
            <;>
            (try simp_all [Finset.sum_range_succ, logb])
            <;>
            (try field_simp)
            <;>
            (try ring_nf)
            <;>
            (try norm_num)
            <;>
            (try linarith)
            <;>
            (try nlinarith)
            <;>
            (try
              {
                norm_num [logb, Real.logb, Real.log_div, Real.log_mul, Real.log_rpow, Real.log_pow] at *
                <;>
                  ring_nf at *
                <;>
                  nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 3), Real.log_pos (by norm_num : (1 : ℝ) < 5)]
              })
            <;>
            (try
              {
                norm_num [logb, Real.logb, Real.log_div, Real.log_mul, Real.log_rpow, Real.log_pow] at *
                <;>
                  ring_nf at *
                <;>
                  nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 3), Real.log_pos (by norm_num : (1 : ℝ) < 5)]
              })
    calc
      (∑ k ∈ Finset.Icc (1 : ℕ) (20 : ℕ), logb ((5 : ℝ) ^ k) ((3 : ℝ) ^ k ^ (2 : ℕ))) * (∑ k ∈ Finset.Icc (1 : ℕ) (100 : ℕ), logb ((9 : ℝ) ^ k) ((25 : ℝ) ^ k)) = (210 : ℝ) * ((Real.log 3) / (Real.log 5)) * ((100 : ℝ) * ((Real.log 25) / (Real.log 9))) := by
        rw [h₁, h₂]
        <;> ring_nf
      _ = (21000 : ℝ) := by
        have h₃ : Real.log 25 = 2 * Real.log 5 := by
          have h₃₁ : Real.log 25 = Real.log (5 ^ 2) := by norm_num
          rw [h₃₁]
          have h₃₂ : Real.log (5 ^ 2) = 2 * Real.log 5 := by
            rw [Real.log_pow] <;> ring_nf <;> norm_num
          rw [h₃₂]
          <;> ring_nf
        have h₄ : Real.log 9 = 2 * Real.log 3 := by
          have h₄₁ : Real.log 9 = Real.log (3 ^ 2) := by norm_num
          rw [h₄₁]
          have h₄₂ : Real.log (3 ^ 2) = 2 * Real.log 3 := by
            rw [Real.log_pow] <;> ring_nf <;> norm_num
          rw [h₄₂]
          <;> ring_nf
        rw [h₃, h₄]
        <;> ring_nf
        <;> field_simp
        <;> ring_nf
        <;> field_simp
        <;> nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 3), Real.log_pos (by norm_num : (1 : ℝ) < 5)]
  exact h_main
