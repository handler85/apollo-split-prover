import os
import glob

# Directory containing the .lean files
DIR = "final_proofs_o3_minif2f_desorrified"

# Get all .lean files in the directory
files = glob.glob(os.path.join(DIR, "*.lean"))

for file_path in files:
    with open(file_path, "r", encoding="utf-8") as f:
        content = f.read()
    new_content = content.replace("sorry", "")
    if new_content != content:
        with open(file_path, "w", encoding="utf-8") as f:
            f.write(new_content)
print("All occurrences of 'sorry' have been removed from .lean files in selected directory.")
