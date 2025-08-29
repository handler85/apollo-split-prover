import os
import subprocess
import json
import argparse
from typing import List, Dict, Any
from tqdm import tqdm
from pathlib import Path
import concurrent.futures

def check_if_already_have(file_path, search_string):
    if not os.path.exists(file_path) or os.path.getsize(file_path) == 0:
        return False
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
            if search_string in content:
                return True
            else:
                return False
    except FileNotFoundError:
        return False

def process_lean_file(file_path: str, lean_cmd: str, exec_path: str, timeout: int) -> Dict[str, Any]:
    
    problem_name = os.path.splitext(os.path.basename(file_path))[0]
    
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            proof_content = f.read()
    except IOError as e:
        return {
            "problem_name": problem_name,
            "status": "failed",
            "error_message": f"Error reading file: {e}",
            "generated_proof": ""
        }

    try:
        process = subprocess.run(
            ['lake', 'env', 'lean', file_path],
            capture_output=True,
            text=True,
            check=False,
            cwd=exec_path,
            timeout=timeout
        )

        if process.returncode == 0:
            anchor_line = "open BigOperators Real Nat Topology Rat"
            
            anchor_pos = proof_content.find(anchor_line)

            is_commented_out = False
            if anchor_pos != -1:
                text_after_anchor = proof_content[anchor_pos + len(anchor_line):]
                
                if text_after_anchor.strip().startswith('/-') and proof_content.strip().endswith('-/'):
                    is_commented_out = True

            if is_commented_out:
                status = "failed"
                error_message = "Error: No proof generated (stuck in repetitive loop)"
            else:
                status = "success"
                error_message = ""
        else:
            status = "failed"
            error_message = (process.stdout + process.stderr).strip()

    except FileNotFoundError:
        return {
            "problem_name": problem_name,
            "status": "failed",
            "error_message": f"Lean command '{lean_cmd}' not found. Please ensure Lean is installed and in your system's PATH.",
            "generated_proof": proof_content
        }
    except subprocess.TimeoutExpired:
        return {
            "problem_name": problem_name,
            "status": "failed",
            "error_message": f"Lean compilation timed out after {timeout} seconds.",
            "generated_proof": proof_content
        }

    return {
        "problem_name": problem_name,
        "status": status,
        "error_message": error_message,
        "generated_proof": proof_content
    }

def main():

    parser = argparse.ArgumentParser(
        description="Run the Lean compiler on a directory of .lean files and record the results in a JSON file.",
        formatter_class=argparse.RawTextHelpFormatter
    )
    parser.add_argument(
        "input_dir",
    )
    parser.add_argument(
        "output_file",
    )
    parser.add_argument(
        "--lean_cmd",
        default="lake env lean",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=120,
    )

    args = parser.parse_args()

    if not os.path.isdir(args.input_dir):
        print(f"Error: Input directory '{args.input_dir}' not found.")
        return

    lean_files = [f for f in os.listdir(args.input_dir) if f.endswith('.lean')]

    if not lean_files:
        print(f"No .lean files found in '{args.input_dir}'.")
        return

    all_results = []
    print(f"Found {len(lean_files)} .lean files to process...")
    #exec_path hardcoded
    EXEC_PATH = '/root/apollo-split-prover/repl'
    if not os.path.isdir(EXEC_PATH):
        print(f"Error: Execution directory '{EXEC_PATH}' not found. Please ensure it exists and is a valid Lean project.")
        return
    num_workers = os.cpu_count()
    
    # Use a ProcessPoolExecutor to run compilations in parallel
    with concurrent.futures.ProcessPoolExecutor(max_workers=num_workers) as executor:
        # Create a future for each file processing task
        future_to_file = {
            executor.submit(process_lean_file, os.path.join(args.input_dir, filename), args.lean_cmd, EXEC_PATH, args.timeout): filename 
            for filename in lean_files
        }
        
        # Use tqdm to show progress as tasks complete
        for future in tqdm(concurrent.futures.as_completed(future_to_file), total=len(lean_files), desc="Compiling Lean files"):
            try:
                result = future.result()
                all_results.append(result)
            except Exception as exc:
                filename = future_to_file[future]
                print(f"\nError processing {filename}: {exc}")

    # Now write all results to the file at the end
    try:
        with open(args.output_file, 'w', encoding='utf-8') as f:
            json.dump(all_results, f, indent=4, ensure_ascii=False)
        print(f"\nSuccessfully processed {len(all_results)} files.")
        print(f"Results have been saved to '{args.output_file}'")
    except IOError as e:
        print(f"\nError writing to output file '{args.output_file}': {e}")

'''
    for filename in tqdm(lean_files, desc="Compiling Lean files"):
        file_path = os.path.join(args.input_dir, filename)
        
        #if check_if_already_have("deepseek_proofs_eval2.json", f'"{os.path.splitext(os.path.basename(file_path))[0]}"'):
         #   print(f"Found '{os.path.splitext(os.path.basename(file_path))[0]}' in the file. Will not dump new data.")
        
        #else:
            
        result = process_lean_file(file_path, args.lean_cmd, EXEC_PATH, args.timeout)
        all_results.append(result)
        try:
            with open(args.output_file, 'w', encoding='utf-8') as f:
                json.dump(all_results, f, indent=4, ensure_ascii=False)
        except IOError as e:
            print(f"\nError writing to output file '{args.output_file}': {e}")
    try:
        with open(args.output_file, 'w', encoding='utf-8') as f:
            json.dump(all_results, f, indent=4, ensure_ascii=False)
        print(f"\nSuccessfully processed {len(all_results)} files.")
        print(f"Results have been saved to '{args.output_file}'")
    except IOError as e:
        print(f"\nError writing to output file '{args.output_file}': {e}")

'''
if __name__ == "__main__":
    main()