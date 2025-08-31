import os
import json
from transformers import AutoModelForCausalLM, AutoTokenizer
import torch
import time
import re


def get_dsv2_initial_answer(problem) -> str:
    model_id = "deepseek-ai/DeepSeek-Prover-V2-7B" 
    tokenizer = AutoTokenizer.from_pretrained(model_id)
    model = AutoModelForCausalLM.from_pretrained(
        model_id, 
        device_map="auto", 
        torch_dtype=torch.bfloat16, 
        trust_remote_code=True
    )
    prompt_template = """
    Complete the following Lean 4 code:
    ```lean4
    {}
    ```
    Before producing the Lean 4 code to formally prove the given theorem, provide a detailed proof plan outlining the main proof steps and strategies.
    The plan should highlight key ideas, intermediate lemmas, and proof structures that will guide the construction of the final formal proof.
    """.strip()
   
    formal_statement = f"""
{problem.get('formal_statement')}  sorry
""".strip()
    chat = [
        {"role": "user", "content": prompt_template.format(formal_statement)},
    ]
    device = next(model.parameters()).device
    inputs = tokenizer.apply_chat_template(
        chat, 
        tokenize=True, 
        add_generation_prompt=True, 
        return_tensors="pt"
    ).to(device)
    with torch.no_grad():  
        outputs = model.generate(
            inputs, 
            max_new_tokens=8192,
            #do_sample=True,  
            #temperature=0.7,
            pad_token_id=tokenizer.eos_token_id
        )
    generated_text = tokenizer.batch_decode(outputs, skip_special_tokens=True)[0]
    input_text = tokenizer.batch_decode(inputs, skip_special_tokens=True)[0]
    resp = generated_text[len(input_text):].strip()

    # Use rpartition to get the text after the last ```lean
    before, sep, after = resp.rpartition('```lean4')

    if sep:  # If ```lean was found
        # Now, find the closing ``` in the 'after' part
        lean_code = after.split('```')[0].strip()
    else:
        # Fallback if ```lean is not present
        lean_code = resp.strip()

    return lean_code
    
    
