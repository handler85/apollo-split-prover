import os

# Lines to deduplicate
TARGET_LINES = [
    "import Mathlib",
    "import Aesop",
    "set_option maxHeartbeats 0",
    "open BigOperators Real Nat Topology Rat"
]

def deduplicate_lines_in_file(filepath, target_lines):
    with open(filepath, "r", encoding="utf-8") as f:
        lines = f.readlines()

    seen = {line: False for line in target_lines}
    new_lines = []
    for l in lines:
        stripped = l.strip()
        if stripped in target_lines:
            if not seen[stripped]:
                new_lines.append(l)
                seen[stripped] = True
            # else: skip duplicate
        else:
            new_lines.append(l)

    if new_lines != lines:
        with open(filepath, "w", encoding="utf-8") as f:
            f.writelines(new_lines)
        print(f"Updated: {filepath}")

def process_directory(root_dir, target_lines):
    for dirpath, _, filenames in os.walk(root_dir):
        for filename in filenames:
            if filename.endswith(".lean"):
                filepath = os.path.join(dirpath, filename)
                deduplicate_lines_in_file(filepath, target_lines)

if __name__ == "__main__":
    import sys
    if len(sys.argv) != 2:
        print("Usage: python dedup_lean_imports.py <directory>")
        exit(1)
    process_directory(sys.argv[1], TARGET_LINES)