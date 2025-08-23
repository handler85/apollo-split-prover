from prover.utils import AttrDict
from prover.algorithms import Sampling

# verifier
lean_max_concurrent_requests = 8
lean_memory_limit = 10
lean_timeout = 120

# model
batch_size = 4
mode = 'cot_ds_v2' # chat templates can be changed in prover/utils.py
pass_ = 1
model_path = 'deepseek-ai/DeepSeek-Prover-V2-7B'

model_args = AttrDict(
    mode=mode,  
    temperature=1,
    max_tokens=8192,
    top_p=0.95,
)

# algorithm
n_search_procs = 16
sampler = dict(
    algorithm=Sampling,
    sample_num=pass_,
    log_interval=32,
)