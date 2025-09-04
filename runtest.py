import os
import json
from apollo import ApolloRepair
from splitprover.gemini_answer import get_gemini_sorrified_lean_sketch
from splitprover.o3_mini_answer import get_o3mini_sorrified_lean_sketch

header = '''
import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
'''


# Parameters
max_attempts = 2 # maximum recursion depth
config = 'configs/baseline_sampling_ds_v2.py' # config file for LLM
output_dir = 'final_proofs'
os.makedirs(output_dir, exist_ok=True)

problem_name = "testprob"
formal_statement = "import Mathlib\nimport Aesop\n\nset_option maxHeartbeats 0\n\nopen BigOperators Real Nat Topology Rat\n\n/-- Suppose that $\\sec x+\\tan x=\\frac{22}7$ and that $\\csc x+\\cot x=\\frac mn,$ where $\\frac mn$ is in lowest terms.  Find $m+n^{}_{}.$ Show that it is 044.-/\ntheorem aime_1991_p9 (x : \u211d) (m : \u211a) (h\u2080 : 1 / Real.cos x + Real.tan x = 22 / 7)\n    (h\u2081 : 1 / Real.sin x + 1 / Real.tan x = m) : \u2191m.den + m.num = 44 := by\n"
#take out \/?
try:
    code = formal_statement
    log_dir = os.path.join('logs', problem_name)
    print('starting manager')
    manager = ApolloRepair(
        code=code,
        lemma_name=problem_name,
        config=config,
        rec_depth=max_attempts,
        log_dir = log_dir
    )
    print('finished manager')
    final_proof_path = manager.run()
    print('ran manager')
    output_path = os.path.join(output_dir, f"{problem_name}.lean")
    with open(final_proof_path, 'r', encoding='utf-8') as src, open(output_path, 'w', encoding='utf-8') as dst:
        dst.write(src.read())
    print(f"Saved proof to {output_path}")
except Exception as e:
    print(f"Error processing {problem_name}: {e}")
        