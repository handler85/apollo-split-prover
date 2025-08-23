#!/bin/bash

NUM_PROBLEMS=$(wc -l < minif2f_train.jsonl)
for ((i=0; i<NUM_PROBLEMS; i++)); do
    echo "Processing problem $i"
    python run.py $i
done