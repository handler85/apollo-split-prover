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

lemma amc12_2000_p12_3
  (a m c : ℕ)
  (h₀ : a + m + c = (12 : ℕ))
  (smoothing_lemma :
  ∀ (x y z : ℕ),
    x ≤ y →
      y ≤ z →
        x + y + z = (12 : ℕ) →
          x * y + x * y * z + x * z + y * z ≤
            x * y + x * y * (z - (1 : ℕ)) + x * (z - (1 : ℕ)) + y + y * (z - (1 : ℕ)) * (2 : ℕ) + (z - (1 : ℕ)))
  (wlog_order :
  ∃ (a' : ℕ) (m' : ℕ),
    a' ≤ m' ∧
      ∃ (x : ℕ),
        m' ≤ x ∧ a' + m' + x = (12 : ℕ) ∧ a * m + a * m * c + a * c + m * c ≤ a' * m' * x + a' * m' + m' * x + a' * x) :
  a * m + a * m * c + a * c + m * c ≤ (112 : ℕ) := by
  have h_main : a * m + a * m * c + a * c + m * c ≤ 112 := by
    have h₁ : a ≤ 12 := by
      omega
    have h₂ : m ≤ 12 := by
      omega
    have h₃ : c ≤ 12 := by
      omega
    interval_cases a <;> interval_cases m <;>
    (try omega) <;>
    (try {
      have h₄ : c ≤ 12 := by omega
      interval_cases c <;> norm_num at * <;>
      (try omega) <;>
      (try nlinarith)
    }) <;>
    (try {
      simp_all [mul_assoc]
      <;>
      ring_nf at * <;>
      nlinarith
    }) <;>
    (try {
      nlinarith
    }) <;>
    (try {
      omega
    })
  
  exact h_main
