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
theorem mathd_numbertheory_765 (x : ℤ) (h₀ : x < 0) (h₁ : 24 * x % 1199 = 15) : x ≤ -449 := by 
  have h_gcd : Int.gcd 24 1199 = 1  := by
      decide
  have h_inv : (24 * 50) % 1199 = 1  := by
      omega
  have h_mul : (50 * (24 * x)) % 1199 = (15 * 50) % 1199  := by
      omega
  have h_modeq : x ≡ 750 [ZMOD 1199]  := by
      try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
      sorry
  have h_exists : ∃ k : ℤ, x = 750 + 1199 * k  := by
      exact Int.modEq_iff_add_fac.mp (id (Int.ModEq.symm h_modeq))
  have h_k_bound : ∀ k : ℤ, (x = 750 + 1199 * k ∧ x < 0) → k ≤ -1  := by
      omega
  have h_conclusion : x ≤ 750 - 1199  := by
      omega
  exact h_conclusion