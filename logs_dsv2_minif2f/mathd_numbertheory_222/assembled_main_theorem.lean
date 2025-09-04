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
theorem mathd_numbertheory_222 (b : ℕ) (h₀ : Nat.lcm 120 b = 3720) (h₁ : Nat.gcd 120 b = 8) :
    b = 248 := by
  have h_main : b = 248 := by
    have h₂ : 120 * b = 3720 * 8 := by
      have h₃ : Nat.lcm 120 b * Nat.gcd 120 b = 120 * b := by
        rw [Nat.mul_comm]
        <;> simp [Nat.gcd_mul_lcm]
        <;> ring
      rw [h₀, h₁] at h₃
      norm_num at h₃ ⊢
      <;> linarith
    have h₄ : b = 248 := by
      have h₅ : 120 * b = 29760 := by
        norm_num at h₂ ⊢
        <;> linarith
      have h₆ : b ≤ 29760 := by
        nlinarith
      interval_cases b <;> norm_num at h₅ h₁ h₀ ⊢ <;>
        (try omega) <;>
        (try {
          simp_all [Nat.lcm, Nat.gcd_eq_right, Nat.gcd_eq_left]
          <;> norm_num at * <;>
            (try omega) <;>
            (try {
              ring_nf at *
              <;> omega
            })
        }) <;>
        (try {
          omega
        })
      <;>
      (try {
        simp_all [Nat.lcm, Nat.gcd_eq_right, Nat.gcd_eq_left]
        <;> norm_num at * <;>
          (try omega) <;>
          (try {
            ring_nf at *
            <;> omega
          })
      })
      <;>
      (try {
        omega
      })
    exact h₄
  exact h_main