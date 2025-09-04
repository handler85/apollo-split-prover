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
theorem mathd_numbertheory_99 (n : ℕ) (h₀ : 2 * n % 47 = 15) : n % 47 = 31 := by
    have h₁ : n % 47 = 31 := by
        have h₂ : 2 * n % 47 = 15  := by
      
            gcongr
        have h₃ : n % 47 = 31 := by
            have h₄ : 2 * n % 47 = 15  := by
        
                gcongr
            have h₅ : n % 47 = 31 := by
                omega
            exact h₅
        exact h₃
    exact h₁