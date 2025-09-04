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
theorem mathd_numbertheory_135 (n A B C : ℕ) 
    (h₀ : n = 3 ^ 17 + 3 ^ 10)
    (h₁ : 11 ∣ n + 1)
    (h₂ : [A, B, C].Pairwise (· ≠ ·))
    (h₃ : {A, B, C} ⊂ Finset.Icc 0 9)
    (h₄ : Odd A ∧ Odd C)
    (h₅ : ¬3 ∣ B)
    (h₆ : Nat.digits 10 n = [B, A, B, C, C, A, C, B, A]) :
    100 * A + 10 * B + C = 129 := by 
    have h_digits : Nat.digits 10 n = [2, 1, 2, 9, 9, 1, 9, 2, 1] := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


        
        have h_main : digits (10 : ℕ) (129199212 : ℕ) = [B, A, B, C, C, A, C, B, A] := by
          have h₇ := h₆.1
          have h₈ := h₆.2.1
          have h₉ := h₆.2.2.1
          have h₁₀ := h₆.2.2.2.1
          have h₁₁ := h₆.2.2.2.2.1
          have h₁₂ := h₆.2.2.2.2.2.1
          have h₁₃ := h₆.2.2.2.2.2.2.1
          have h₁₄ := h₆.2.2.2.2.2.2.2
          have h₁₅ := h₆.2.2.2.2.2.2.2
          simp at h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ h₁₃ h₁₄ h₁₅
          <;>
          (try omega) <;>
          (try
            {
              norm_num [digits_zero] at *
              <;>
              (try contradiction) <;>
              (try omega) <;>
              (try
                {
                  rcases C with (_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | C) <;>
                  rcases A with (_ | _ | _ | A) <;>
                  rcases B with (_ | _ | _ | B) <;>
                  norm_num [digits_zero] at * <;>
                  simp_all (config := {decide := true}) <;>
                  omega
                }) <;>
              (try
                {
                  aesop
                })
            }) <;>
          (try
            {
              aesop
            }) <;>
          (try
            {
              norm_num [digits_zero] at * <;>
              rcases C with (_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | C) <;>
              rcases A with (_ | _ | _ | A) <;>
              rcases B with (_ | _ | _ | B) <;>
              norm_num [digits_zero] at * <;>
              simp_all (config := {decide := true}) <;>
              aesop
            })
          <;>
          (try omega) <;>
          (try aesop)
          <;>
          (try norm_num [digits_zero] at *) <;>
          (try omega) <;>
          (try aesop)
          <;>
          (try omega)
          <;>
          (try aesop)
          <;>
          (try omega)
          <;>
          (try aesop)
          <;>
          (try omega)
          <;>
          (try aesop)
          <;>
          (try omega)
          <;>
          (try aesop)
        
        exact h_main


    have h_extract : (A, B, C) = (1, 2, 9) := by
        simp_all only [ne_eq, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true, List.Pairwise.nil, and_self, and_true, AddLeftCancelMonoid.add_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, List.cons.injEq, and_self_left]
    have h_conditions : Odd 1 ∧ Odd 9 ∧ (¬3 ∣ 2) := by
        decide
  
    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


    
    --have h_contradiction : False := by
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
        (try omega) <;>
        (try
            {
                omega
            }) <;>
        (try
            {
                omega
            }) <;>
        (try
            {
                norm_num [Nat.dvd_iff_mod_eq_zero, Nat.mod_eq_of_lt] at h₁
                <;> omega
            })
        <;>
        (try
            {
                simp_all [Nat.odd_iff_not_even, Nat.even_iff]
                <;> omega
            })
        <;>
        (try
            {
                omega
            })
        <;>
        (try
            {
                aesop
            })
        <;>
        (try
            {
                omega
            })
    


