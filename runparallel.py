import os
import json
from concurrent.futures import ProcessPoolExecutor, as_completed
from apollo import ApolloRepair
from splitprover.gemini_answer import get_gemini_sorrified_lean_sketch
from splitprover.o3_mini_answer import get_o3mini_sorrified_lean_sketch

#code = '''
#import Mathlib
#import Aesop
#
#set_option maxHeartbeats 0
#
#open BigOperators Real Nat Topology Rat
#'''
max_attempts = 3 # maximum recursion depth
config = 'configs/baseline_sampling_ds_v2.py' # config file for LLM
output_dir = 'final_proofs'
os.makedirs(output_dir, exist_ok=True)

def process_problem(problem):
    problem_name = problem['name']
    formal_statement = problem['formal_statement']
    #take out \/?
    try:
        o3_sketch = get_o3mini_sorrified_lean_sketch(problem_name, formal_statement)
        code = o3_sketch + "\n"
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
        return f"Saved proof to {output_path}"
    except Exception as e:
        return f"Error processing {problem_name}: {e}"
# Parameters

with open('minif2f_train.jsonl', 'r', encoding='utf-8') as f:
    problems = [json.loads(line) for line in f]
num_workers = os.cpu_count()
with ProcessPoolExecutor(max_workers=num_workers) as executor:
    futures = [executor.submit(process_problem, problem) for problem in problems]
    for idx, future in enumerate(as_completed(futures)):
        print(future.result())
