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

lemma mathd_algebra_76_1
  (f : ℤ → ℤ)
  (h₀ : ∀ (n : ℤ), Odd n → f n = n ^ (2 : ℕ))
  (h₁ : ∀ (n : ℤ), Even n → f n = n ^ (2 : ℕ) - (4 : ℤ) * n - (1 : ℤ))
  (ev4 : Even (4 : ℕ)) :
  f (4 : ℤ) = Int.subNatNat (16 : ℕ) (16 : ℕ) - (1 : ℤ) := by
  have h₂ : f (4 : ℤ) = -1 := by
    have h₃ : Even (4 : ℤ) := by
      simp [Int.even_iff]
      <;> norm_num
    have h₄ : f (4 : ℤ) = (4 : ℤ) ^ (2 : ℕ) - (4 : ℤ) * (4 : ℤ) - (1 : ℤ) := by
      apply h₁
      exact h₃
    rw [h₄]
    norm_num
    <;> ring
    <;> norm_num
  
  have h₃ : Int.subNatNat (16 : ℕ) (16 : ℕ) - (1 : ℤ) = -1 := by
    norm_num [Int.subNatNat]
    <;> rfl
  
  have h₄ : f (4 : ℤ) = Int.subNatNat (16 : ℕ) (16 : ℕ) - (1 : ℤ) := by
    rw [h₂]
    <;> simp_all
    <;> norm_num
    <;> rfl
  
  exact h₄
