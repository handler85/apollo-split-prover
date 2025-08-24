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


with open('minif2f_train.jsonl', 'r', encoding='utf-8') as f:
    problems = [json.loads(line) for line in f]
problem_index = int(sys.argv[1])
problem = problems[problem_index]
problem_name = problem['name']
logs_dir = os.path.join(os.getcwd(), "logs")
problem_dir = os.path.join(logs_dir, problem_name)
if os.path.isdir(problem_dir):
    print(f"Deleting: {problem_dir}")
    shutil.rmtree(problem_dir, ignore_errors=True)
else:
    print("Directory to be deleted not found in current directory.")
delete_pycache(".")
with open("timed_out.txt", "a") as file:
    file.write(f"\n{problem_name}")
