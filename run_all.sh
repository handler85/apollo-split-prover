#!/bin/bash

NUM_PROBLEMS=$(wc -l < minif2f_train.jsonl)
for ((i=0; i<NUM_PROBLEMS; i++)); do
    echo "Processing problem $i"
    python3 run.py $i
    rm -rf ~/.cache/vllm
    pkill -f "python.*launch_solver" || true
    sleep 2
done