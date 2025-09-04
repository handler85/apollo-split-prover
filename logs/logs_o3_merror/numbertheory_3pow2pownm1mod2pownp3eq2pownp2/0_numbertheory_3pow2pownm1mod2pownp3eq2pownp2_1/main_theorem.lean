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
lemma numbertheory_3pow2pownm1mod2pownp3eq2pownp2_1
  (n : ℕ)
  (h₀ : (0 : ℕ) < n) :
  ((3 : ℕ) ^ (2 : ℕ) ^ n - (1 : ℕ)) % (2 : ℕ) ^ (n + (3 : ℕ)) = (2 : ℕ) ^ (n + (2 : ℕ)) := by
  try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
  try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
  sorry