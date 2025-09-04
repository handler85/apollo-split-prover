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
theorem mathd_numbertheory_12 :
    Finset.card (Finset.filter (fun x => 20 ∣ x) (Finset.Icc 15 85)) = 4 := by
    have div_def : ∀ x, (20 ∣ x) ↔ (∃ k : ℤ, x = 20 * k) := by
    
        exact fun (x : ℤ) => dvd_iff_exists_eq_mul_right
    have candidates_eq : Finset.filter (fun x => 20 ∣ x) (Finset.Icc 15 85) = {20, 40, 60, 80} := by
    
        decide
    have card_candidates : Finset.card {20, 40, 60, 80} = 4 := by
    
        decide
    rw [candidates_eq, card_candidates]