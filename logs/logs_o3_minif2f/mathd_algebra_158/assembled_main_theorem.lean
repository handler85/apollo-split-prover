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
theorem mathd_algebra_158 (a : ℕ) (h₀ : Even a)
    (h₁ : ∑ k in Finset.range 8, (2 * k + 1) - ∑ k in Finset.range 5, (a + 2 * k) = (4 : ℤ)) :
    a = 8 := by
    have h_sum_odd : ∑ k in Finset.range 8, (2 * k + 1) = 64 := by


        
        have h_sum_main : ∑ k ∈ Finset.range (8 : ℕ), ((2 : ℕ) * k + (1 : ℕ)) = 64 := by
          decide
        rw [h_sum_main]
        <;> norm_num
        <;>
        (try omega) <;>
        (try
          {
            simp_all [Finset.sum_range_succ, mul_add, mul_one, mul_comm, mul_left_comm, mul_assoc,
              Int.ofNat_add, Int.ofNat_mul, Int.ofNat_sub]
            <;>
            ring_nf at *
            <;>
            norm_cast at *
            <;>
            omega
          }) <;>
        (try omega)
        <;>
        (try
          {
            rcases h₀ with ⟨k, rfl⟩
            <;>
            simp_all [Finset.sum_range_succ, mul_add, mul_one, mul_comm, mul_left_comm, mul_assoc,
              Int.ofNat_add, Int.ofNat_mul, Int.ofNat_sub]
            <;>
            ring_nf at *
            <;>
            norm_cast at *
            <;>
            omega
          })
        <;>
        (try omega)
        <;>
        (try
          {
            norm_num [Finset.sum_range_succ, Finset.sum_range_zero] at *
            <;>
            ring_nf at *
            <;>
            omega
          })
        <;>
        (try omega)
        <;>
        (try
          {
            simp_all [Finset.sum_range_succ, mul_add, mul_one, mul_comm, mul_left_comm, mul_assoc,
              Int.ofNat_add, Int.ofNat_mul, Int.ofNat_sub]
            <;>
            ring_nf at *
            <;>
            norm_cast at *
            <;>
            omega
          })
        <;>
        (try omega)


    have h_sum_even : ∑ k in Finset.range 5, (a + 2 * k) = 5 * a + 20 := by


        
        have h_sum_range_8 : (∑ k ∈ Finset.range (8 : ℕ), ((2 : ℕ) * k + (1 : ℕ))) = 64 := by
          simp [Finset.sum_range_succ, mul_add, mul_one, add_assoc]
          <;> norm_num
          <;> rfl
        
        have h_sum_goal : ∑ k ∈ Finset.range (5 : ℕ), (a + (2 : ℕ) * k) = (5 : ℕ) * a + (20 : ℕ) := by
          simp [Finset.sum_range_succ, mul_add, mul_one, add_assoc] at h₁ ⊢
          <;> ring_nf at h₁ ⊢ <;>
          (try omega) <;>
          (try
            {
              norm_num at h₁ ⊢ <;>
              rcases h₀ with ⟨k, hk⟩ <;>
              simp [hk, mul_add, mul_comm, mul_left_comm, mul_assoc, Nat.mul_sub_left_distrib, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at h₁ ⊢ <;>
              ring_nf at h₁ ⊢ <;>
              omega
            }) <;>
          (try omega) <;>
          (try
            {
              omega
            })
          <;>
          omega
        
        exact h_sum_goal


    have h_equation : 64 - (5 * a + 20) = 4 := by
    
    


        
        have h_main : (64 : ℕ) - ((5 : ℕ) * a + (20 : ℕ)) = (4 : ℕ) := by
          have h₂ := h₁
          simp [h_sum_odd, h_sum_even, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ] at h₂ ⊢
          <;>
          (try omega) <;>
          (try
            {
              norm_num at h₂ ⊢ <;>
              ring_nf at h₂ ⊢ <;>
              norm_cast at h₂ ⊢ <;>
              omega
            }) <;>
          (try
            {
              rcases h₀ with ⟨k, rfl⟩
              norm_num at h₂ ⊢ <;>
              ring_nf at h₂ ⊢ <;>
              norm_cast at h₂ ⊢ <;>
              omega
            }) <;>
          (try
            {
              rcases h₀ with ⟨k, rfl⟩
              norm_num at h₂ ⊢ <;>
              ring_nf at h₂ ⊢ <;>
              norm_cast at h₂ ⊢ <;>
              ring_nf at h₂ ⊢ <;>
              omega
            })
          <;>
          omega
        exact h_main


    have h_simplified : 44 - 5 * a = 4 := by


        
        have h_main : (44 : ℕ) - (5 : ℕ) * a = (4 : ℕ) := by
          have h₂ : (64 : ℕ) - ((5 : ℕ) * a + (20 : ℕ)) = (4 : ℕ) := h_equation
          have h₃ : (5 : ℕ) * a + (20 : ℕ) ≤ 64 := by
            by_contra h
            have h₄ : (5 : ℕ) * a + (20 : ℕ) > 64 := by omega
            have h₅ : (64 : ℕ) - ((5 : ℕ) * a + (20 : ℕ)) = 0 := by
              have h₆ : (5 : ℕ) * a + (20 : ℕ) > 64 := by omega
              have h₇ : (64 : ℕ) - ((5 : ℕ) * a + (20 : ℕ)) = 0 := by
                apply Nat.sub_eq_zero_of_le
                omega
              exact h₇
            omega
          have h₄ : (5 : ℕ) * a + (20 : ℕ) ≤ 64 := h₃
          have h₅ : (44 : ℕ) - (5 : ℕ) * a = (4 : ℕ) := by
            have h₆ : (64 : ℕ) - ((5 : ℕ) * a + (20 : ℕ)) = (4 : ℕ) := h₂
            have h₇ : (5 : ℕ) * a + (20 : ℕ) ≤ 64 := h₄
            have h₈ : (5 : ℕ) * a ≤ 44 := by omega
            omega
          exact h₅
        exact h_main


    have h_solve : 5 * a = 40 := by


        
        have h_main : (5 : ℕ) * a = (40 : ℕ) := by
          have h₂ : (44 : ℕ) - (5 : ℕ) * a = (4 : ℕ) := h_simplified
          have h₃ : (5 : ℕ) * a ≤ 44 := by
            by_contra h
            have h₄ : (5 : ℕ) * a ≥ 45 := by omega
            have h₅ : (44 : ℕ) - (5 : ℕ) * a = 0 := by
              have h₆ : (5 : ℕ) * a ≥ 45 := by omega
              have h₇ : (44 : ℕ) - (5 : ℕ) * a = 0 := by
                omega
              exact h₇
            omega
          have h₄ : (5 : ℕ) * a = 40 := by
            have h₅ : (44 : ℕ) - (5 : ℕ) * a = (4 : ℕ) := h_simplified
            have h₆ : (5 : ℕ) * a ≤ 44 := by omega
            interval_cases (5 : ℕ) * a <;> norm_num at h₅ ⊢ <;> omega
          exact h₄
        exact h_main


    have h_divide : a = 8 := by


        
        have h_main : a = 8 := by
          have h₂ : a = 8 := by
            have h₃ : 5 * a = 40 := by simpa [mul_comm] using h_solve
            have h₄ : a = 8 := by
              omega
            exact h₄
          exact h₂
        exact h_main


    exact h_divide