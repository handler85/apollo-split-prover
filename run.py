import os
from apollo import ApolloRepair
from gemini_answer import get_gemini_sorrified_lean_sketch
from o3_mini_answer import get_o3mini_sorrified_lean_sketch

#code = '''
#import Mathlib
#import Aesop
#
#set_option maxHeartbeats 0
#
#open BigOperators Real Nat Topology Rat
#'''

problem_name = "amc12a_2003_p5"
formal_statement = "import Mathlib\nimport Aesop\n\nset_option maxHeartbeats 0\n\nopen BigOperators Real Nat Topology Rat\n\n/-- The sum of the two 5-digit numbers $AMC10$ and $AMC12$ is $123422$. What is $A+M+C$? \n\n$ \\mathrm{(A) \\ } 10\\qquad \\mathrm{(B) \\ } 11\\qquad \\mathrm{(C) \\ } 12\\qquad \\mathrm{(D) \\ } 13\\qquad \\mathrm{(E) \\ } 14 $ Show that it is \\mathrm{(E)}\\ 14.-/\ntheorem amc12a_2003_p5 (A M C : \u2115) (h\u2080 : A \u2264 9 \u2227 M \u2264 9 \u2227 C \u2264 9)\n    (h\u2081 : Nat.ofDigits 10 [0, 1, C, M, A] + Nat.ofDigits 10 [2, 1, C, M, A] = 123422) :\n    A + M + C = 14 := by\n"

o3_sketch = get_o3mini_sorrified_lean_sketch(problem_name, formal_statement)
code = o3_sketch + "\n"
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