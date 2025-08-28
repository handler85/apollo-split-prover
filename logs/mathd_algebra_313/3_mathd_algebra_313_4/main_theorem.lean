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
lemma mathd_algebra_313_4
    (v i z : ℂ)
    (h₀ : v = i * z)
    (h₁ : v = (1 : ℂ) + Complex.I)
    (h₂ : z = (2 : ℂ) - Complex.I)
    (h_sub : (1 : ℂ) + Complex.I = i * ((2 : ℂ) - Complex.I))
    (h_div : i = ((1 : ℂ) + Complex.I) / ((2 : ℂ) - Complex.I))
    (h_mult : i = ((1 : ℂ) + Complex.I) * ((2 : ℂ) + Complex.I) / (((2 : ℂ) - Complex.I) * ((2 : ℂ) + Complex.I)))
    (h_denom : ((2 : ℂ) - Complex.I) * ((2 : ℂ) + Complex.I) = (5 : ℂ))
    (h_num : ((1 : ℂ) + Complex.I) * ((2 : ℂ) + Complex.I) = (1 : ℂ) + (3 : ℂ) * Complex.I) :
    i = ((1 : ℂ) + (3 : ℂ) * Complex.I) / (5 : ℂ) := by
  exact Eq.symm (Mathlib.Tactic.Ring.div_congr (id (Eq.symm h_num)) (id (Eq.symm h_denom)) (id (Eq.symm h_mult)))