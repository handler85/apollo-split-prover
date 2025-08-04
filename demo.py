import os
from apollo import ApolloRepair

code = '''
import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_141 (a b : ℝ) (h₁ : a * b = 180) (h₂ : 2 * (a + b) = 54) :
    a ^ 2 + b ^ 2 = 369 := by
  have h3 : a + b = 27 := by
    field_simp [h₂]
  have h4 : (a + b) ^ 2 = 729 := by
    rw [h3]
    norm_num
  have expand : a ^ 2 + b ^ 2 = (a + b) ^ 2 - 2 * a * b := by
    ring
  have step1 : a ^ 2 + b ^ 2 = 729 - 2 * a * b := by
    rw [expand, h4]
  have step2 : 729 - 2 * a * b = 729 - 360 := by
    rw [h₁]
  have step3 : 729 - 360 = 369 := by
    norm_num
  exact step1.trans (step2.trans step3)
'''


# Rec Depth
max_attempts = 2
config = 'configs/baseline_sampling_kimina_prover.py'
problem_dir = 'logs/test'

# Instantiate the single-lemma manager
manager = ApolloRepair(
    code=code,
    lemma_name='test',
    config=config,
    rec_depth=max_attempts,
    log_dir = problem_dir
)

# Run the entire fix/verify pipeline and get the final assembled proof path
final_proof_path = manager.run()

with open(final_proof_path, 'r') as f:
    proof = f.read()
print(proof)

'''
Final output should look like this:

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
theorem mathd_algebra_141 (a b : ℝ) (h₁ : a * b = 180) (h₂ : 2 * (a + b) = 54) :
    a ^ 2 + b ^ 2 = 369 := by
    have h3 : a + b = 27 := by
        linarith
    have h4 : (a + b) ^ 2 = 729 := by
        rw [h3]
        norm_num
    have expand : a ^ 2 + b ^ 2 = (a + b) ^ 2 - 2 * a * b := by
        ring
    have step1 : a ^ 2 + b ^ 2 = 729 - 2 * a * b := by
        rw [expand, h4]
    have step2 : 729 - 2 * a * b = 729 - 360 := by
        linarith
    have step3 : 729 - 360 = 369 := by
        norm_num
    linarith
'''