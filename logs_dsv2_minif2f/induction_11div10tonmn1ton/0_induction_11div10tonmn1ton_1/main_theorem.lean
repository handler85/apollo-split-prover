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
lemma induction_11div10tonmn1ton_1
    (ih : ∀ m < (3 : ℕ) + n, (11 : ℤ) ∣ -(-1 : ℤ) ^ m + (10 : ℤ) ^ m) :
    (11 : ℤ) ∣ (-1 : ℤ) ^ n + (10 : ℤ) ^ n * (1000 : ℤ) := by
  try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
  try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
  sorry