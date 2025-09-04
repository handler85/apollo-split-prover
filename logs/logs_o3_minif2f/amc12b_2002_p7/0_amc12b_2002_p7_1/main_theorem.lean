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
lemma amc12b_2002_p7_1
  (a b c : ℕ)
  (h₀ : (0 : ℕ) < a)
  (sum_simp : True)
  (prod_eq : a * (2 : ℕ) + a ^ (2 : ℕ) * (3 : ℕ) + a ^ (3 : ℕ) = (24 : ℕ) + a * (24 : ℕ))
  (h_bc : c = (2 : ℕ) + a)
  (h₁ : b = (1 : ℕ) + a) :
  a * (2 : ℕ) + a ^ (2 : ℕ) * (3 : ℕ) + a ^ (3 : ℕ) = (24 : ℕ) + a * (24 : ℕ) := by
  gcongr