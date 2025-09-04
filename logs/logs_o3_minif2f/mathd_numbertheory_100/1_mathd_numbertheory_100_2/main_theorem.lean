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

lemma mathd_numbertheory_100_2
  (n : ℕ)
  (h₀ : (0 : ℕ) < n)
  (h₁ : n.gcd (40 : ℕ) = (10 : ℕ))
  (h₂ : n.lcm (40 : ℕ) = (280 : ℕ))
  (h_gcd_lcm : n.gcd (40 : ℕ) * n.lcm (40 : ℕ) = n * (40 : ℕ)) :
  (10 : ℕ) * (280 : ℕ) = n * (40 : ℕ) := by
  have h_main : (10 : ℕ) * (280 : ℕ) = n * (40 : ℕ) := by
    have h₃ : n.gcd 40 * n.lcm 40 = n * 40 := by
      simpa [Nat.gcd_comm] using h_gcd_lcm
    have h₄ : n.gcd 40 = 10 := by simpa using h₁
    have h₅ : n.lcm 40 = 280 := by simpa using h₂
    rw [h₄, h₅] at h₃
    <;> norm_num at h₃ ⊢ <;> nlinarith
  
  exact h_main
