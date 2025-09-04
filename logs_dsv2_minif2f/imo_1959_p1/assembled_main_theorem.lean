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
theorem imo_1959_p1 (n : ℕ) (h₀ : 0 < n) : Nat.gcd (21 * n + 4) (14 * n + 3) = 1 := by
  have h_main : Nat.gcd (21 * n + 4) (14 * n + 3) = 1 := by
    have h₁ : Nat.gcd (21 * n + 4) (14 * n + 3) = Nat.gcd (14 * n + 3) (7 * n + 1) := by
      have h₂ : 21 * n + 4 = 1 * (14 * n + 3) + (7 * n + 1) := by
        ring_nf
        <;> omega
      rw [h₂]
      simp [Nat.gcd_comm, Nat.gcd_add_mul_right_right]
      <;>
      simp [Nat.gcd_comm, Nat.gcd_add_mul_right_right]
      <;>
      ring_nf
      <;>
      omega
    rw [h₁]
    have h₃ : Nat.gcd (14 * n + 3) (7 * n + 1) = 1 := by
      have h₄ : 14 * n + 3 = 2 * (7 * n + 1) + 1 := by
        ring_nf
        <;> omega
      rw [h₄]
      have h₅ : Nat.gcd (2 * (7 * n + 1) + 1) (7 * n + 1) = Nat.gcd (7 * n + 1) 1 := by
        simp [Nat.gcd_comm, Nat.gcd_add_mul_right_right]
        <;>
        simp [Nat.gcd_comm, Nat.gcd_add_mul_right_right]
        <;>
        ring_nf
        <;>
        omega
      rw [h₅]
      simp
    rw [h₃]
    <;>
    simp
    <;>
    ring_nf
    <;>
    omega
  exact h_main