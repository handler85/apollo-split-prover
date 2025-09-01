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
theorem mathd_numbertheory_435 (k : ℕ) (h₀ : 0 < k) (h₁ : ∀ n, Nat.gcd (6 * n + k) (6 * n + 3) = 1)
    (h₂ : ∀ n, Nat.gcd (6 * n + k) (6 * n + 2) = 1) (h₃ : ∀ n, Nat.gcd (6 * n + k) (6 * n + 1) = 1) :
    5 ≤ k := by
    have h_main : 5 ≤ k := by
        by_contra! h
        have h₄ : k ≤ 4  := by
            linarith
        have h₅ : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by
            omega
        rcases h₅ with (rfl | rfl | rfl | rfl)
        --· -- Case k = 1
            --
            --
            --
            --
            --
            --
            --
            --
            --
            --
            --<;>
      
      
      
      
        --· -- Case k = 2
            --
            --
            --
            --
            --
            --
            --
            --
            --
            --
            --<;>
      
      
      
      
        --· -- Case k = 3
            --
            --
            --
            --
            --
            --
            --
            --
            --
            --
            --<;>
      
      
      
      
        --· -- Case k = 4
            --
            --
            --
            --
            --
            --
            --
            --
            --
            --
            --<;>
      
      
      
      
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


        
        have h₅ : False := by
          have h₆ := h₂ 0
          norm_num [Nat.gcd_eq_right] at h₆
          <;> contradiction
        exact h₅


        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


        
        have h_false : False := by
          have h₅ := h₂ 0
          have h₆ := h₂ 1
          have h₇ := h₂ 2
          have h₈ := h₂ 3
          have h₉ := h₂ 4
          norm_num at h₅ h₆ h₇ h₈ h₉
          <;>
          (try contradiction) <;>
          (try omega) <;>
          (try
            {
              simp_all [Nat.gcd_eq_right, Nat.gcd_eq_left]
              <;>
              omega
            })
          <;>
          aesop
        exact h_false


        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
        

    exact h_main