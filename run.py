import os
import json
from apollo import ApolloRepair
from gemini_answer import get_gemini_sorrified_lean_sketch
from o3_mini_answer import get_o3mini_sorrified_lean_sketch

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

with open('minif2f_train.jsonl', 'r', encoding='utf-8') as f:
    problems = [json.loads(line) for line in f]

for idx, problem in enumerate(problems):
    problem_name = problem['name']
    formal_statement = problem['formal_statement']
    #take out \/?
    print(f"Processing {idx+1}/{len(problems)}: {problem_name}")
    try:
        o3_sketch = get_o3mini_sorrified_lean_sketch(problem_name, formal_statement)
        code = header + "\n" + o3_sketch + "\n"
        log_dir = os.path.join('logs', problem_name)
        manager = ApolloRepair(
            code=code,
            lemma_name=problem_name,
            config=config,
            rec_depth=max_attempts,
            log_dir = log_dir
        )
        final_proof_path = manager.run()
        output_path = os.path.join(output_dir, f"{problem_name}.lean")
        with open(final_proof_path, 'r', encoding='utf-8') as src, open(output_path, 'w', encoding='utf-8') as dst:
            dst.write(src.read())
        print(f"Saved proof to {output_path}")
    except Exception as e:
        print(f"Error processing {problem_name}: {e}")
        