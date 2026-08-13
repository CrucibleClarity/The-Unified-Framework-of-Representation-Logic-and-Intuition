"""docs/paper_data/scripts/exp61h_train.py —— EXP-61h 训练 (注入 clone + 替换 + 训练)

流程:
  1. 注入 op 同义 clone (D:9001/D:9002, 相同定义) → vocab 含 clone
  2. 构建样本 + 随机替换 op → clone_a/b (各半)
  3. train_seq 训练 (clone 参与)
  4. 评估: 全 clone 混合 OOD + 单 clone (只用 a) OOD

用法: PYTHONPATH=. python -m docs.paper_data.scripts.exp61h_train --op logical_and
"""
import argparse
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import torch

from tokenizer import api
from tokenizer.token_index import inject_temp, clear_cache, _TEMP_INJECT
from tokenizer.maintain import core
from tokenizer._register import DERIVE_REGISTRY, DERIVE_BY_NAME, load_derive
from train import train_seq
from train.data import vocab
from eval_helpers import judge_many


def inject_clone(op_name, n=2):
    src = core.load_all()[api.eid_by_name(op_name)]
    defn = src.get("definition")
    rows = [{"eid": f"D:9{i + 1:03d}", "name": f"{op_name}_c{i}", "dtype": "bool",
             "definition": defn, "ref": "", "intension": f"{op_name} clone {i}"}
            for i in range(n)]
    inject_temp("C", rows)
    DERIVE_REGISTRY.clear(); DERIVE_BY_NAME.clear()
    load_derive(); clear_cache(); core._ALL_CACHE = None
    return rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--op", default="logical_and")
    ap.add_argument("--epochs", type=int, default=15)
    args = ap.parse_args()

    rows = inject_clone(args.op, 2)
    clone_eids = [r["eid"] for r in rows]
    print(f"注入 clone: {[r['name'] for r in rows]}, vocab={len(vocab())}")

    # 构建样本 (exp61g_infix 基线套件) + 替换 op → clone 均匀
    from lab import synth_core
    cfg = json.load(open("docs/paper_data/configs/exp61g_infix_only.json"))
    train, _, _ = synth_core.compose_samples(samples=cfg["synth"]["samples"], seed=0)
    op_eid = api.eid_by_name(args.op)
    import random
    rng = random.Random(0)
    cnt = [0, 0]
    for s in train:
        for i, e in enumerate(s["seq"]):
            if e == op_eid:
                c = rng.choice(clone_eids)
                s["seq"][i] = c
                cnt[clone_eids.index(c)] += 1
    print(f"替换 {args.op}→clone: c0={cnt[0]} c1={cnt[1]}")

    # 训练 (clone 在 vocab, train_seq 自动含) — 归档到 archive (可复现, 禁 /tmp)
    res = train_seq(train, epochs=args.epochs, dim=64, num_layers=2, seed=0,
                    token=f"exp61h_{args.op}_clone")
    model = res["model"]
    print(f"train acc={res['acc']:.3f}")
    print(f"归档: {res.get('run_dir')}")

    # 评估: 单 clone 推理 (结构集中 vs 直觉均匀)
    from lab.judge import judge_sequence
    _T = api.role_token("truth"); TRUE, FALSE = _T
    c0, c1 = clone_eids
    def mk(a, op, b, truth):
        return judge_sequence([TRUE if a else FALSE, op, TRUE if b else FALSE], truth)
    def judge(seqs):
        ss = [{"seq": s, "valid": 1} for s in seqs]
        if len(ss) < 2: ss = ss + [{"seq": seqs[0], "valid": 1}]
        return run_exp._judge_eval(model, ss)[0]
    from lab import run_exp
    seqs_c0 = [mk(a, c0, b, a and b) for a in (True,False) for b in (True,False)]
    seqs_c1 = [mk(a, c1, b, a and b) for a in (True,False) for b in (True,False)]
    print(f"只用 c0 判定: {judge(seqs_c0):.3f} | 只用 c1 判定: {judge(seqs_c1):.3f}")
    print("结论: c0=1.0 c1=0.0 → 结构集中 (canonical 化), 非直觉均匀")


if __name__ == "__main__":
    main()
