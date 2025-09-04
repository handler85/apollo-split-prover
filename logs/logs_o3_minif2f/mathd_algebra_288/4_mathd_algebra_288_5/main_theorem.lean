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

lemma mathd_algebra_288_5
  (x y : ℝ)
  (n : NNReal)
  (hy : y = (-6 : ℝ))
  (hx : x = (-4 : ℝ))
  (x_sq_eq sq_eq h2_simpl : True)
  (h₃ : √(52 : ℝ) = √(↑n : ℝ))
  (h₂ : True) :
  n = (52 : NNReal) := by
  have h_main : (n : ℝ) = 52 := by
    have h₄ : √(52 : ℝ) = √(↑n : ℝ) := h₃
    have h₅ : (√(52 : ℝ) : ℝ) = √(↑n : ℝ) := by exact_mod_cast h₄
    have h₆ : (0 : ℝ) ≤ 52 := by norm_num
    have h₇ : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast NNReal.coe_nonneg n
    have h₈ : √(52 : ℝ) = √(↑n : ℝ) := h₅
    have h₉ : (√(52 : ℝ) : ℝ) ^ 2 = (√(↑n : ℝ) : ℝ) ^ 2 := by rw [h₈]
    have h₁₀ : (√(52 : ℝ) : ℝ) ^ 2 = (52 : ℝ) := by
      rw [Real.sq_sqrt (by positivity)]
    have h₁₁ : (√(↑n : ℝ) : ℝ) ^ 2 = (↑n : ℝ) := by
      rw [Real.sq_sqrt (by positivity)]
    have h₁₂ : (52 : ℝ) = (↑n : ℝ) := by linarith
    have h₁₃ : (n : ℝ) = 52 := by linarith
    exact h₁₃
  
  have h_final : n = (52 : NNReal) := by
    apply_fun (fun x => (x : ℝ)) at h_main
    norm_cast at h_main ⊢
    <;>
    (try simp_all) <;>
    (try aesop) <;>
    (try ring_nf at * <;> norm_num at * <;> nlinarith) <;>
    (try simp_all [NNReal.coe_inj]) <;>
    (try aesop)
    <;>
    (try linarith)
    <;>
    (try norm_num at * <;> nlinarith)
    <;>
    (try simp_all [Real.sqrt_eq_iff_sq_eq, pow_two])
    <;>
    (try ring_nf at * <;> nlinarith)
    <;>
    (try aesop)
    <;>
    (try nlinarith)
    <;>
    (try norm_num)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
  
  apply h_final
