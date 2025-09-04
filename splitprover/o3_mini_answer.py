import os
# pip install --upgrade openai
from openai import OpenAI


def get_o3mini_sorrified_lean_sketch(problem_name: str, formal_statement: str) -> str:
   
    api_key = os.getenv("OPENAI_API_KEY")
    if not api_key:
        raise ValueError("Please set the OPENAI_API_KEY environment variable.")

    client = OpenAI()
    prompt = f"""
You are a Lean 4 proof assistant. Here is a math problem:

Problem Name: {problem_name}

```lean
{formal_statement}
```

First, provide a step-by-step natural language solution to the problem, breaking it down into all necessary lemmas and logical steps.

Then, based on your NL solution, write a Lean 4 proof outline for the formal statement above.
- The Lean proof skeleton should have the same structure as your NL solution, with each lemma and step reflected as a corresponding Lean lemma or proof step.
- Do not define lemmas prior to defining the main theorem - the proof structure must begin with the main theorem statement, and all necessary lemmas must be defined after the := by.
- For all steps, use 'sorry' as a placeholder - your job is to only provide the proof structure.
- Use clear Lean 4 syntax and include all necessary lemma statements and structure.

Start your Lean4 code with the tag ```lean, and end it with ```.
"""
    resp = client.responses.create(
        model="o3-mini",
        reasoning={"effort": "high"},   # low | medium | high
        input=prompt,
        max_output_tokens=8192
    )
    print(resp.output_text)

    import re
    match = re.search(r"```lean(.*?)```", resp.output_text, re.DOTALL)
    if match:
        lean_code = match.group(1).strip()
    else:
        lean_code = resp.output_text.strip()
    return lean_code