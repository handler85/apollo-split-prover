'''
    This code is adopted from https://github.com/deepseek-ai/DeepSeek-Prover-V1.5
'''
import os
import re
import json
import pytz
from pathlib import Path
from datetime import datetime
from collections import UserDict
from importlib.machinery import SourceFileLoader
from easydict import EasyDict as AttrDict


LEAN4_DEFAULT_HEADER = "import Mathlib\nimport Aesop\n\nset_option maxHeartbeats 0\n\nopen BigOperators Real Nat Topology Rat\n\n"

def non_cot_prompt(data):
    return "Complete the following Lean 4 code:\n\n```lean4\n{header}{informal_prefix}{formal_statement}".format(
        header=data.get('header', LEAN4_DEFAULT_HEADER),
        informal_prefix=data.get('informal_prefix', str()),
        formal_statement=data['formal_statement'],
    )

def non_cot_few_shot_prompt(data):
    return "Complete the following Lean 4 code:\n\n```lean4\n{header}{informal_prefix}{formal_statement}{formal_proof}\n```\n\n\n".format(
        header=data.get('header', LEAN4_DEFAULT_HEADER),
        informal_prefix=data.get('informal_prefix', str()),
        formal_statement=data['formal_statement'],
        formal_proof=data['formal_proof'],
    )

def cot_prompt(data):
    return "Complete the following Lean 4 code with explanatory comments preceding each line of code:\n\n```lean4\n{header}{informal_prefix}{formal_statement}".format(
        header=data.get('header', LEAN4_DEFAULT_HEADER),
        informal_prefix=data.get('informal_prefix', str()),
        formal_statement=data['formal_statement'],
    )

def cot_few_shot_prompt(data):
    return "Complete the following Lean 4 code with explanatory comments preceding each line of code:\n\n```lean4\n{header}{informal_prefix}{formal_statement}{formal_proof}\n```\n\n\n".format(
        header=data.get('header', LEAN4_DEFAULT_HEADER),
        informal_prefix=data.get('informal_prefix', str()),
        formal_statement=data['formal_statement'],
        formal_proof=data['formal_proof'],
    )

def cot_kimina_prompt(data):
    return "Think about and solve the following problem step by step in Lean 4.\n# Problem:{informal_prefix}\n# Formal statement:\n```lean4\n{header}{formal_statement}\n```\n".format(
        header=data.get('header', LEAN4_DEFAULT_HEADER),
        informal_prefix=data.get('informal_prefix', str()),
        formal_statement=data['formal_statement'],
    )

def cot_kimina_few_shot_prompt(data):
    return "Think about and solve the following problem step by step in Lean 4.\n# Problem:{informal_prefix}\n# Formal statement:\n```lean4\n{header}{formal_statement}{formal_proof}\n```\n".format(
        header=data.get('header', LEAN4_DEFAULT_HEADER),
        informal_prefix=data.get('informal_prefix', str()),
        formal_statement=data['formal_statement'],
        formal_proof=data['formal_proof'],
    )

def post_process_output(output):
    _find_idx = output.find("```")
    return output[:_find_idx] if _find_idx >= 0 else output

def kimina_post_process_output(output):
    def after_by(s: str) -> str:
        m = re.search(r':=\s*by(.*)', s, flags=re.DOTALL)
        return m.group(1) if m else s
    output = output[:output.find('<\think>')]
    _find_idx = output.find("```")

    # return output[:_find_idx] if _find_idx >= 0 else output
    pattern = r"```lean4\s*(.*?)\s*```"
    match = re.search(pattern, output, flags=re.DOTALL)
    output = match.group(1) if match else output

    output = after_by(output)
    return output

MODEL_FORMAT = dict(
    non_cot=dict(prompt=non_cot_prompt, output=post_process_output, few_shot=non_cot_few_shot_prompt),
    cot=dict(prompt=cot_prompt, output=post_process_output, few_shot=cot_few_shot_prompt),
    cot_kimina=dict(prompt=cot_kimina_prompt, output=kimina_post_process_output, few_shot=cot_kimina_few_shot_prompt)
)

def get_datetime(human_readable=False, tz_name=None):
    if tz_name:
        tz = pytz.timezone(tz_name)
        now = datetime.now(tz)
    else:
        now = datetime.now()
    
    fmt = "%Y/%m/%d %H:%M:%S" if human_readable else "%Y%m%d_%H%M%S"
    return now.strftime(fmt)

def load_config(fname):
    name = Path(fname).stem
    mod = SourceFileLoader(name, fname).load_module()

    config = {}
    for n in dir(mod):
        if not n.startswith("__"):
            config[n] = getattr(mod, n)
    config = AttrDict(config)

    return config

def load_jsonl_objects(input_path):
    objects = []
    with open(input_path, 'r', encoding='utf-8') as fr:
        for line in fr:
            objects.append(json.loads(line))
    return objects


class ConcurrentJob(object):
    def __init__(self, stage_list):
        assert len(stage_list) > 1
        self.stage_list = stage_list
        self.reset()
    
    def is_idle(self):
        return self._stage_idx is None
    
    def reset(self):
        self._stage_idx = None
        self._stage_cache = None
    
    def start(self, **kwargs):
        self._stage_idx = 1
        self._stage_cache = self.stage_list[0](**kwargs)
    
    def get_status(self):
        assert not self.is_idle()
        while True:
            status = self.stage_list[self._stage_idx](**self._stage_cache)
            if status is None:
                return None
            self._stage_idx += 1
            if self._stage_idx == len(self.stage_list):
                self.reset()
                return status
            self._stage_cache = status