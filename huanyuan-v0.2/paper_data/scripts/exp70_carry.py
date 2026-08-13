"""docs/paper_data/scripts/exp70_carry.py —— EXP-70 最长 carry/borrow 链

真实状态传播 (weights≈program): 999...9+1 全程进位链, 1000...0-1 borrow 链.
用法: PYTHONPATH=. python -m docs.paper_data.scripts.exp70_carry --run <dir>
"""
import argparse
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import torch
from tokenizer import api
from lab.judge import judge_sequence
from lab.synth_core import nested_seq
from eval_helpers import load_model, judge_many


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--run", default="archive/log/train/fold_num_v5_20260811_191742")
    args = ap.parse_args()
    model = load_model(args.run)
    ADD = api.eid_by_name("addition")
    SUB = api.eid_by_name("subtraction")

    print("=== EXP-70 carry 链 (999...9 + 1) ===")
    for nd in (2, 20, 100, 2000):
        a = int("9" * nd); b = 1
        seq = judge_sequence(nested_seq([a, b], ADD, a + b), True)
        a_ = judge_many(model, [seq])[0]
        print(f"  {nd}位全9+1: acc={a_:.3f}")

    print("=== borrow 链 (1000...0 - 1) ===")
    for nd in (2, 20, 100, 2000):
        a = 10 ** nd; b = 1
        seq = judge_sequence(nested_seq([a, b], SUB, a - b), True)
        a_ = judge_many(model, [seq])[0]
        print(f"  {nd+1}位1000..0-1: acc={a_:.3f}")


if __name__ == "__main__":
    main()
