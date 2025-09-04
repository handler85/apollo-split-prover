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

lemma mathd_algebra_289_1
  (k t m n : ℕ)
  (h₀ : Nat.Prime m ∧ Nat.Prime n)
  (h₁ : t < k)
  (h₂ : (↑k : ℤ) ^ (2 : ℕ) - (↑m : ℤ) * (↑k : ℤ) + (↑n : ℤ) = (0 : ℤ))
  (h₃ : (↑t : ℤ) ^ (2 : ℕ) - (↑m : ℤ) * (↑t : ℤ) + (↑n : ℤ) = (0 : ℤ)) :
  k + t = m := by
  have h_main : k + t = m := by
    have h₄ : (k : ℤ) ^ 2 - (m : ℤ) * k + n = 0 := by simpa [add_comm] using h₂
    have h₅ : (t : ℤ) ^ 2 - (m : ℤ) * t + n = 0 := by simpa [add_comm] using h₃
    have h₆ : (k : ℤ) > t := by exact_mod_cast h₁
    have h₇ : (k : ℤ) - t > 0 := by linarith
    have h₈ : ((k : ℤ) - t) * ((k : ℤ) + t - m) = 0 := by
      have h₉ := h₄
      have h₁₀ := h₅
      ring_nf at h₉ h₁₀ ⊢
      nlinarith
    have h₉ : (k : ℤ) - t > 0 := by linarith
    have h₁₀ : (k : ℤ) + t - m = 0 := by
      have h₁₁ := h₈
      have h₁₂ : ((k : ℤ) - t) ≠ 0 := by linarith
      have h₁₃ : ((k : ℤ) - t) * ((k : ℤ) + t - m) = 0 := h₈
      have h₁₄ : ((k : ℤ) + t - m) = 0 := by
        apply mul_left_cancel₀ h₁₂
        nlinarith
      nlinarith
    have h₁₁ : (k : ℤ) + t = m := by linarith
    have h₁₂ : k + t = m := by
      have h₁₃ : (k : ℤ) + t = m := h₁₁
      have h₁₄ : (k : ℤ) + t = m := by linarith
      have h₁₅ : k + t = m := by
        norm_cast at h₁₃ h₁₄ ⊢
        <;> linarith
      exact h₁₅
    exact h₁₂
  exact h_main
