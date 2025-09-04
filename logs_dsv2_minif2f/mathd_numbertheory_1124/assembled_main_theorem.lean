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
theorem mathd_numbertheory_1124 (n : ℕ) (h₀ : n ≤ 9) (h₁ : 18 ∣ 374 * 10 + n) : n = 4 := by
    have h_main : n = 4 := by
        have h₂ : n ≤ 9  := by
      
            gcongr
        have h₃ : 18 ∣ 374 * 10 + n  := by
      
            gcongr
        have h₄ : n ≤ 9  := by
      
            gcongr
        interval_cases n <;> norm_num at h₃ ⊢ <;>
        (try omega) <;>
        (try {
            omega
        }) <;>
        (try {
            omega
        }) <;>
        (try {
            norm_num at h₃
            <;> omega
        })
        <;>
        (try {
            omega
        })
        <;>
        (try {
            norm_num at h₃
            <;> omega
        })
    exact h_main