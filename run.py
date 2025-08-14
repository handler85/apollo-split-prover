import os
from apollo import ApolloRepair
from gemini_answer import get_gemini_sorrified_lean_sketch
code = '''
import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
'''
problem_name = "cool_problem"
nl_statement = "\/-- Show that 1+1=2. -\/\n"
formal_statement = "import Mathlib\nimport Aesop\n\nset_option maxHeartbeats 0\n\nopen BigOperators Real Nat Topology Rat\n\n\/-- Show that 1+1=2. -\/\ntheorem cool_problem : 1+1=2 := by\n"

gem_sketch = get_gemini_sorrified_lean_sketch(problem_name, nl_statement, formal_statement)
code += '\n' + gem_sketch + '\n'
# Parameters
max_attempts = 2 # maximum recursion depth
config = 'configs/baseline_sampling_ds_v2.py' # config file for LLM
problem_dir = 'logs/test' # where to save final lean file and intermediate proof states

# Instantiate the Apollo repair object
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