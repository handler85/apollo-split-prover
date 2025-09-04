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
theorem mathd_numbertheory_711 (m n : ℕ) 
    (h₀ : 0 < m ∧ 0 < n) 
    (h₁ : Nat.gcd m n = 8)
    (h₂ : Nat.lcm m n = 112) : 72 ≤ m + n := by 
    have div_m : 8 ∣ m  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


        
        have h_main : (8 : ℕ) ∣ m := by
          have h₃ : (m.gcd n : ℕ) ∣ m := Nat.gcd_dvd_left m n
          have h₄ : (m.gcd n : ℕ) = 8 := by simpa using h₁
          rw [h₄] at h₃
          exact h₃
        exact h_main


    have div_n : 8 ∣ n  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


        
        have h_main : (8 : ℕ) ∣ n := by
          have h₃ : 8 ∣ n := by
            have h₄ : 8 ∣ m := by simpa [Nat.dvd_iff_mod_eq_zero] using div_m
            have h₅ : 8 ∣ n := by
              have h₆ : 8 ∣ Nat.gcd m n := by simpa [h₁] using h₄
              have h₇ : 8 ∣ n := by
                -- Use the property that gcd(m, n) divides both m and n.
                have h₈ : 8 ∣ Nat.gcd m n := by simpa [h₁] using h₆
                have h₉ : Nat.gcd m n ∣ n := Nat.gcd_dvd_right m n
                exact Nat.dvd_trans h₈ h₉
              exact h₇
            exact h₅
          exact h₃
        exact h_main


    obtain ⟨a, ha⟩ : ∃ a, m = 8 * a := by exact div_m
    obtain ⟨b, hb⟩ : ∃ b, n = 8 * b := by exact div_n
    have coprime_ab : Nat.gcd a b = 1  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


        
        have h_main : a.gcd b = 1 := by
          have h₃ : (a * 8).gcd (b * 8) = 8 := by simpa [mul_comm] using h₁
          have h₄ : (a * 8).gcd (b * 8) = 8 * (a.gcd b) := by
            rw [← Nat.gcd_mul_left]
            <;> simp [mul_comm]
          rw [h₄] at h₃
          have h₅ : 8 * (a.gcd b) = 8 := by linarith
          have h₆ : a.gcd b = 1 := by
            apply Nat.eq_of_mul_eq_mul_left (show 0 < 8 by norm_num)
            linarith
          exact h₆
        exact h_main


    have prod_relation : m * n = Nat.gcd m n * Nat.lcm m n  := by
        exact Eq.symm (Nat.gcd_mul_lcm m n)
    rw [h₁, h₂] at prod_relation
    have m_times_n : m * n = 8 * 112  := by
        gcongr
    rw [ha, hb] at m_times_n
    have ab_eq : a * b = 14  := by
        linarith
    have ab_sum_lower_bound : a + b ≥ 9  := by
        try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


        
        have h_sum_ge_nine : 9 ≤ a + b := by
          have h₁ : a ∣ 14 := by
            use b
            linarith
          have h₂ : b ∣ 14 := by
            use a
            linarith
          have h₃ : a ≤ 14 := Nat.le_of_dvd (by norm_num) h₁
          have h₄ : b ≤ 14 := Nat.le_of_dvd (by norm_num) h₂
          interval_cases a <;> interval_cases b <;> norm_num at * <;>
          (try contradiction) <;>
          (try simp_all [Nat.gcd_eq_right, Nat.lcm, Nat.gcd_eq_left]) <;>
          (try omega) <;>
          (try
            {
              simp_all [Nat.gcd_eq_right, Nat.lcm, Nat.gcd_eq_left]
              <;> norm_num at *
              <;> omega
            }) <;>
          (try
            {
              aesop
            })
          <;>
          omega
        exact h_sum_ge_nine


    rw [ha, hb]
    linarith