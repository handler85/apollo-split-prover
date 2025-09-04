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

lemma imo_1959_p1_1
  (n : ℕ)
  (h₀ : (0 : ℕ) < n)
  (h_step1 : True) :
  ((1 : ℕ) + n * (7 : ℕ)).gcd ((3 : ℕ) + n * (14 : ℕ)) = ((3 : ℕ) + n * (14 : ℕ)).gcd ((1 : ℕ) + n * (7 : ℕ)) := by
  have h_main : ((1 : ℕ) + n * (7 : ℕ)).gcd ((3 : ℕ) + n * (14 : ℕ)) = ((3 : ℕ) + n * (14 : ℕ)).gcd ((1 : ℕ) + n * (7 : ℕ)) := by
    rw [Nat.gcd_comm]
    <;>
    simp [Nat.gcd_comm, Nat.gcd_assoc, Nat.gcd_mul_left, Nat.gcd_mul_right, Nat.gcd_one_left, Nat.gcd_one_right]
    <;>
    ring_nf
    <;>
    omega
  
  apply h_main
  <;>
  simp_all
  <;>
  norm_num
  <;>
  linarith
