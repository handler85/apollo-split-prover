import os
import json
from apollo import ApolloRepair
from gemini_answer import get_gemini_sorrified_lean_sketch
from o3_mini_answer import get_o3mini_sorrified_lean_sketch
import shutil
import sys

def delete_root_logs():
    logs_dir = os.path.join(os.getcwd(), "logs")
    if os.path.isdir(logs_dir):
        print(f"Deleting: {logs_dir}")
        shutil.rmtree(logs_dir, ignore_errors=True)
    else:
        print("No 'logs' directory found in current directory.")

def delete_pycache(root="."):
    for dirpath, dirnames, filenames in os.walk(root, topdown=False):
        for dirname in dirnames:
            if dirname == "__pycache__":
                full_path = os.path.join(dirpath, dirname)
                print(f"Deleting: {full_path}")
                shutil.rmtree(full_path, ignore_errors=True)
def fix_slashes(s: str) -> str:
    return s.replace("\\/", "/")

def process_minif2f_problem(idx, problem, total_problems, header, config, max_attempts, output_dir):
    problem_name = problem['name']
    formal_statement = fix_slashes(problem['formal_statement'])
    print(f"Processing {idx+1}/{total_problems}: {problem_name}")
    try:
        o3_sketch = get_o3mini_sorrified_lean_sketch(problem_name, formal_statement)
        code = header + "\n" + o3_sketch + "\n"
        log_dir = os.path.join('logs', problem_name)
        manager = ApolloRepair(
            code=code,
            lemma_name=problem_name,
            config=config,
            rec_depth=max_attempts,
            log_dir=log_dir
        )
        final_proof_path = manager.run()
        output_path = os.path.join(output_dir, f"{problem_name}.lean")
        with open(final_proof_path, 'r', encoding='utf-8') as src, open(output_path, 'w', encoding='utf-8') as dst:
            dst.write(src.read())
        print(f"Saved proof to {output_path}")
    except Exception as e:
        print(f"Error processing {problem_name}: {e}")


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



if len(sys.argv) < 2:
    print("Usage: python run.py <problem_index>")
    sys.exit(1)

problem_index = int(sys.argv[1])

with open('minif2f_train.jsonl', 'r', encoding='utf-8') as f:
    problems = [json.loads(line) for line in f]

if not (0 <= problem_index < len(problems)):
    print(f"Invalid problem index: {problem_index}")
    sys.exit(1)

problem = problems[problem_index]
process_minif2f_problem(problem_index, problem, len(problems), header, config, max_attempts, output_dir)
delete_pycache(".")