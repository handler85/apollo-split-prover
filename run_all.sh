#!/bin/bash

NUM_PROBLEMS=$(wc -l < minif2f_train.jsonl)
for ((i=0; i<NUM_PROBLEMS; i++)); do
    echo "Processing problem $i"
    timeout 20m python3 run.py $i
    if [ $? -eq 124 ]; then
        echo "Timeout reached for problem $i"
        python3 handle_timeout.py $i
    fi
    echo "Killing all Python processes..."
    pkill -9 -f python || true
    rm -rf ~/.cache/vllm
    echo "Waiting for resources to be released..."
    sleep 5
    echo "Starting fresh for next problem..."
done