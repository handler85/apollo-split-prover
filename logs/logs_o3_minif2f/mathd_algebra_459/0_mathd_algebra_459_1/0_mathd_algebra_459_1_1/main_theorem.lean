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
lemma mathd_algebra_459_1_1
    (a b c d : ℚ)
    (h₀ : (3 : ℚ) * a = b + c + d)
    (h₁ : (4 : ℚ) * b = a + c + d)
    (h₂ : (2 : ℚ) * c = a + b + d)
    (h₃ : (8 : ℚ) * a + (10 : ℚ) * b + (6 : ℚ) * c = (24 : ℚ))
    (d_eq1 : d = (3 : ℚ) * a - b - c)
    (d_eq2 : d = (4 : ℚ) * b - a - c)
    (eq1 : (3 : ℚ) * a - b - c = (4 : ℚ) * b - a - c)
    (rel1 : (4 : ℚ) * a = (5 : ℚ) * b)
    (d_eq3 : d = (2 : ℚ) * c - a - b)
    (eq2 : (3 : ℚ) * a - b - c = (2 : ℚ) * c - a - b)
    (rel2 : (4 : ℚ) * a = (3 : ℚ) * c)
    (b_expr : b = (4 : ℚ) * a / (5 : ℚ))
    (c_expr : c = (4 : ℚ) * a / (3 : ℚ))
    (a_eq : a = (1 : ℚ))
    (b_val : b = (4 / 5 : ℚ))
    (c_val : c = (4 / 3 : ℚ))
    (d_val : d = (3 : ℚ) - (4 / 5 : ℚ) - (4 / 3 : ℚ))
    (d_simpl h₅ : d = (13 / 15 : ℚ)) :
    (↑d.den : ℤ) + d.num = (28 : ℤ) := by
    have h_d : d = 13 / 15 := by
        norm_num [a_eq, b_val, c_val, d_val] at *
        <;>
        (try norm_num at *) <;>
        (try linarith) <;>
        (try nlinarith) <;>
        (try ring_nf at *) <;>
        (try linarith)
        <;>
        norm_num [div_eq_mul_inv] at * <;>
        ring_nf at * <;>
        nlinarith
    have h_main : (↑d.den : ℤ) + d.num = 28 := by
        have h₆ : d = 13 / 15  := by
      
            gcongr
        have h₇ : d = 13 / 15  := by
            linarith
        have h₈ : (↑d.den : ℤ) + d.num = 28 := by
            rw [h₇]
            norm_cast
      
            <;> norm_num
            <;> rfl
        exact h₈
    exact h_main