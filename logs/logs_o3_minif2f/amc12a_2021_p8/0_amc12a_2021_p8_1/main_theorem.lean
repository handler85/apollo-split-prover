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

lemma amc12a_2021_p8_1
  (d : ℕ → ℕ)
  (h₀ : d (0 : ℕ) = (0 : ℕ))
  (h₁ : d (1 : ℕ) = (0 : ℕ))
  (h₂ : d (2 : ℕ) = (1 : ℕ))
  (h₃ : ∀ (n : ℕ), (3 : ℕ) ≤ n → d n = d (n - (1 : ℕ)) + d (n - (3 : ℕ))) :
  ∀ (n : ℕ),
    (2 : ℕ) ≤ n → (d ((2 : ℕ) + n) * (4 : ℕ) + d n * (5 : ℕ) + d (n - (2 : ℕ)) * (2 : ℕ)) % (2 : ℕ) = d n % (2 : ℕ) := by
  have h_main : ∀ (n : ℕ), (2 : ℕ) ≤ n → (d ((2 : ℕ) + n) * (4 : ℕ) + d n * (5 : ℕ) + d (n - (2 : ℕ)) * (2 : ℕ)) % (2 : ℕ) = d n % (2 : ℕ) := by
    intro n hn
    have h₄ : (d ((2 : ℕ) + n) * (4 : ℕ) + d n * (5 : ℕ) + d (n - (2 : ℕ)) * (2 : ℕ)) % (2 : ℕ) = d n % (2 : ℕ) := by
      have h₅ : (d ((2 : ℕ) + n) * (4 : ℕ) + d n * (5 : ℕ) + d (n - (2 : ℕ)) * (2 : ℕ)) % (2 : ℕ) = (d ((2 : ℕ) + n) * (4 : ℕ) % 2 + d n * (5 : ℕ) % 2 + d (n - (2 : ℕ)) * (2 : ℕ) % 2) % 2 := by
        simp [Nat.add_mod, Nat.mul_mod]
        <;> omega
      rw [h₅]
      have h₆ : d ((2 : ℕ) + n) * (4 : ℕ) % 2 = 0 := by
        have h₇ : d ((2 : ℕ) + n) * (4 : ℕ) % 2 = 0 := by
          have h₈ : d ((2 : ℕ) + n) % 2 = 0 ∨ d ((2 : ℕ) + n) % 2 = 1 := by omega
          rcases h₈ with (h₈ | h₈) <;> simp [h₈, Nat.mul_mod, Nat.add_mod, Nat.mod_mod]
          <;> omega
        exact h₇
      have h₇ : d n * (5 : ℕ) % 2 = d n % 2 := by
        have h₈ : d n * (5 : ℕ) % 2 = d n % 2 := by
          have h₉ : d n % 2 = 0 ∨ d n % 2 = 1 := by omega
          rcases h₉ with (h₉ | h₉) <;> simp [h₉, Nat.mul_mod, Nat.add_mod, Nat.mod_mod] <;>
            (try omega) <;> (try omega) <;> (try omega) <;> (try omega)
          <;> (try omega)
          <;> (try omega)
          <;> omega
        exact h₈
      have h₈ : d (n - (2 : ℕ)) * (2 : ℕ) % 2 = 0 := by
        have h₉ : d (n - (2 : ℕ)) * (2 : ℕ) % 2 = 0 := by
          have h₁₀ : d (n - (2 : ℕ)) % 2 = 0 ∨ d (n - (2 : ℕ)) % 2 = 1 := by omega
          rcases h₁₀ with (h₁₀ | h₁₀) <;> simp [h₁₀, Nat.mul_mod, Nat.add_mod, Nat.mod_mod]
          <;> omega
        exact h₉
      omega
    exact h₄
  exact h_main
