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

lemma mathd_algebra_215_1_1
  (S : Finset ℝ)
  (x : ℝ)
  (h₂ : x = (-3 : ℝ) - √(7 : ℝ) * (4 : ℝ))
  (h₀ : ∀ (x : ℝ), x ∈ S ↔ (9 : ℝ) + x * (6 : ℝ) + x ^ (2 : ℕ) = (121 : ℝ))
  (hx : (112 : ℝ) = (121 : ℝ))
  (h₁ : (9 : ℝ) = (0 : ℝ)) :
  False := by
  have h₃ : False := by
    norm_num at hx h₁ <;>
    (try contradiction) <;>
    (try linarith) <;>
    (try nlinarith [Real.sqrt_nonneg 7])
    <;>
    simp_all [Finset.mem_singleton]
    <;>
    norm_num at *
    <;>
    nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show 0 ≤ 7 by norm_num)]
  exact h₃
