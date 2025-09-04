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

lemma mathd_algebra_158_6
  (a : ℕ)
  (h₀ : Even a)
  (h₁ :
  (↑(∑ k ∈ Finset.range (8 : ℕ), ((2 : ℕ) * k + (1 : ℕ))) : ℤ) -
      (↑(∑ k ∈ Finset.range (5 : ℕ), (a + (2 : ℕ) * k)) : ℤ) =
    (4 : ℤ))
  (h_sum_odd : ∑ k ∈ Finset.range (8 : ℕ), ((2 : ℕ) * k + (1 : ℕ)) = (64 : ℕ))
  (h_sum_even : ∑ k ∈ Finset.range (5 : ℕ), (a + (2 : ℕ) * k) = (5 : ℕ) * a + (20 : ℕ))
  (h_equation : (64 : ℕ) - ((5 : ℕ) * a + (20 : ℕ)) = (4 : ℕ))
  (h_simplified : (44 : ℕ) - (5 : ℕ) * a = (4 : ℕ))
  (h_solve : (5 : ℕ) * a = (40 : ℕ)) :
  a = (8 : ℕ) := by
  have h_main : a = 8 := by
    have h₂ : a = 8 := by
      have h₃ : 5 * a = 40 := by simpa [mul_comm] using h_solve
      have h₄ : a = 8 := by
        omega
      exact h₄
    exact h₂
  exact h_main
