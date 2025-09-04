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

lemma mathd_numbertheory_764_1_1
  (p : ℕ)
  (h₀ : Nat.Prime p)
  (h₁ : (7 : ℕ) ≤ p)
  (k : ℕ)
  (hk : (1 : ℕ) ≤ k ∧ k ≤ p - (2 : ℕ))
  (h : (↑k : ZMod p) = (0 : ZMod p))
  (h₅ : k < p)
  (h₆ : p ∣ k) :
  p ≤ k := by
  have h_contradiction : False := by
    have h₇ : p ∣ k := h₆
    have h₈ : k ≥ p := by
      have h₉ : p ∣ k := h₇
      have h₁₀ : p ≤ k := Nat.le_of_dvd (by omega) h₉
      omega
    have h₉ : k < p := by
      have h₁₀ : k ≤ p - 2 := hk.2
      have h₁₁ : p ≥ 7 := by omega
      have h₁₂ : p - 2 < p := by
        have h₁₃ : p ≥ 7 := by omega
        have h₁₄ : p - 2 < p := by
          omega
        exact h₁₄
      omega
    omega
  
  have h_main : p ≤ k := by
    exfalso
    exact h_contradiction
  
  exact h_main
