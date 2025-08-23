#!/bin/bash

NUM_PROBLEMS=$(wc -l < minif2f_train.jsonl)
for ((i=0; i<NUM_PROBLEMS; i++)); do
    echo "Processing problem $i"
    python3 run.py $i
    echo "Killing all Python processes..."
    pkill -9 -f python || true
    rm -rf ~/.cache/vllm
    echo "Waiting for resources to be released..."
    sleep 5
    echo "Starting fresh for next problem..."
done