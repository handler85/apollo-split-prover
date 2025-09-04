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

lemma mathd_numbertheory_100_4
  (n : ℕ)
  (h₀ : (0 : ℕ) < n)
  (h₁ : n.gcd (40 : ℕ) = (10 : ℕ))
  (h₂ : n.lcm (40 : ℕ) = (280 : ℕ))
  (h_gcd_lcm : n.gcd (40 : ℕ) * n.lcm (40 : ℕ) = n * (40 : ℕ))
  (h_subst : (10 : ℕ) * (280 : ℕ) = n * (40 : ℕ))
  (h_n_eq : n = (10 : ℕ) * (280 : ℕ) / (40 : ℕ)) :
  (10 : ℕ) * (280 : ℕ) / (40 : ℕ) = (70 : ℕ) := by
  have h_main : (10 : ℕ) * (280 : ℕ) / (40 : ℕ) = (70 : ℕ) := by
    apply Eq.symm
    norm_num
    <;> rfl
  exact h_main
